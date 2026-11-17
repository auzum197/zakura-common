//! `Commit^ivk` of the narrow chip.
//!
//! The constraints are those of the Orchard `Commit^ivk` chip. That chip checks the
//! canonicity of `ak` and `nk` in one gate over two rows of nine columns. Here the
//! same checks are two gates, one for `ak` and one for `nk`, each over three rows of
//! three columns.

use crate::backend::ff::{Field, PrimeField};
use crate::backend::halo2_gadgets::{sinsemilla::HashDomains, utilities::bool_check};
use crate::backend::halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Constraints, Error, Expression},
};
use crate::backend::pasta_curves::pallas;

use super::{Cell, Config, assign, copy, sinsemilla::Piece};
use crate::constants::{OrchardFixedBasesFull, OrchardHashDomains, T_P};

/// Number of bits of `a`: bits 0..=249 of `ak`.
const A_BITS: usize = 250;
/// Number of bits of `b_0`: bits 250..=253 of `ak`.
const B_0_BITS: usize = 4;
/// Number of bits of `b_2`: bits 0..=4 of `nk`.
const B_2_BITS: usize = 5;
/// Number of bits of `c`: bits 5..=244 of `nk`.
const C_BITS: usize = 240;
/// Number of bits of `d_0`: bits 245..=253 of `nk`.
const D_0_BITS: usize = 9;
/// Index of the most significant bit of a base field element.
const TOP_BIT: usize = 254;

/// Number of 10-bit words of the message pieces `a`, `b`, `c`, `d`.
const A_WORDS: usize = 25;
const B_WORDS: usize = 1;
const C_WORDS: usize = 24;
const D_WORDS: usize = 1;

/// Index of the running sum that remains after 130 bits of a piece.
const Z_13: usize = 13;
/// Number of 10-bit words in the 130-bit decomposition of `a_prime`.
const A_PRIME_WORDS: usize = 13;
/// Number of 10-bit words in the 140-bit decomposition of `b2_c_prime`.
const B2_C_PRIME_WORDS: usize = 14;

/// `2^exponent` in the base field.
fn two_pow(exponent: usize) -> pallas::Base {
    pallas::Base::from(2).pow_vartime([exponent as u64])
}

/// The integer made of bits `start..end` of `value`, as a field element.
fn bit_range(value: &pallas::Base, start: usize, end: usize) -> pallas::Base {
    let repr = value.to_repr();
    (start..end).rev().fold(pallas::Base::ZERO, |acc, i| {
        acc.double() + pallas::Base::from(u64::from((repr[i / 8] >> (i % 8)) & 1))
    })
}

impl Config {
    pub(super) fn create_commit_ivk_gates(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        let two_pow_4 = two_pow(B_0_BITS);
        let two_pow_5 = two_pow(B_2_BITS);
        let two_pow_9 = two_pow(D_0_BITS);
        let two_pow_250 = two_pow(A_BITS);
        let two_pow_245 = two_pow(B_2_BITS + C_BITS);
        let two_pow_254 = two_pow(TOP_BIT);
        let t_p = Expression::Constant(pallas::Base::from_u128(T_P));

        // ak = a (250 bits) || b_0 (4 bits) || b_1 (1 bit)
        // b = b_0 || b_1 || b_2
        //
        // | ak    | a       | b           |
        // | b_0   | b_1     | b_2         |
        // | z13_a | a_prime | z13_a_prime |
        //
        // https://p.z.cash/orchard-0.1:commit-ivk-decompositions
        // https://p.z.cash/orchard-0.1:commit-ivk-canonicity-ak?partial
        meta.create_gate("CommitIvk canonicity check of ak", |meta| {
            let q_commit_ivk_ak = meta.query_selector(self.q_commit_ivk_ak);
            let ak = self.adv(meta, 0, 0);
            // `a` is constrained by the Sinsemilla hash to be 250 bits.
            let a = self.adv(meta, 1, 0);
            // `b` is constrained by the Sinsemilla hash to be 10 bits.
            let b_whole = self.adv(meta, 2, 0);
            // b_0 has been constrained outside this gate to be a four-bit value.
            let b_0 = self.adv(meta, 0, 1);
            // This gate constrains b_1 to be a one-bit value.
            let b_1 = self.adv(meta, 1, 1);
            // b_2 has been constrained outside this gate to be a five-bit value.
            let b_2 = self.adv(meta, 2, 1);
            // z13_a is the 13th running sum output by the 10-bit Sinsemilla
            // decomposition of `a`.
            let z13_a = self.adv(meta, 0, 2);
            let a_prime = self.adv(meta, 1, 2);
            let z13_a_prime = self.adv(meta, 2, 2);

            let b1_bool_check = bool_check(b_1.clone());
            // Check that b_whole is consistent with the witnessed subpieces.
            let b_decomposition_check =
                b_whole - (b_0.clone() + b_1.clone() * two_pow_4 + b_2 * two_pow_5);
            // Check that ak = a (250 bits) || b_0 (4 bits) || b_1 (1 bit)
            let ak_decomposition_check =
                a.clone() + b_0.clone() * two_pow_250 + b_1.clone() * two_pow_254 - ak;

            // The `ak` canonicity checks are enforced if and only if `b_1` = 1.
            // b_1 = 1 => b_0 = 0
            let b0_canon_check = b_1.clone() * b_0;
            // b_1 = 1 => z13_a = 0
            let z13_a_check = b_1.clone() * z13_a;
            // Check that a_prime = a + 2^130 - t_P.
            // This is checked regardless of the value of b_1.
            let a_prime_check = {
                let two_pow_130 = Expression::Constant(two_pow(A_PRIME_WORDS * 10));
                a + two_pow_130 - t_p.clone() - a_prime
            };
            // Check that the running sum output by the 130-bit little-endian
            // decomposition of `a_prime` is zero.
            let z13_a_prime_check = b_1 * z13_a_prime;

            Constraints::with_selector(
                q_commit_ivk_ak,
                [
                    ("b1_bool_check", b1_bool_check),
                    ("b_decomposition_check", b_decomposition_check),
                    ("ak_decomposition_check", ak_decomposition_check),
                    ("b0_canon_check", b0_canon_check),
                    ("z13_a_check", z13_a_check),
                    ("a_prime_check", a_prime_check),
                    ("z13_a_prime", z13_a_prime_check),
                ],
            )
        });

        // nk = b_2 (5 bits) || c (240 bits) || d_0 (9 bits) || d_1 (1 bit)
        // d = d_0 || d_1
        //
        // | nk    | c          | d              |
        // | d_0   | d_1        | b_2            |
        // | z13_c | b2_c_prime | z14_b2_c_prime |
        //
        // https://p.z.cash/orchard-0.1:commit-ivk-decompositions
        // https://p.z.cash/orchard-0.1:commit-ivk-canonicity-nk?partial
        meta.create_gate("CommitIvk canonicity check of nk", |meta| {
            let q_commit_ivk_nk = meta.query_selector(self.q_commit_ivk_nk);
            let nk = self.adv(meta, 0, 0);
            // `c` is constrained by the Sinsemilla hash to be 240 bits.
            let c = self.adv(meta, 1, 0);
            // `d` is constrained by the Sinsemilla hash to be 10 bits.
            let d_whole = self.adv(meta, 2, 0);
            // d_0 has been constrained outside this gate to be a nine-bit value.
            let d_0 = self.adv(meta, 0, 1);
            // This gate constrains d_1 to be a one-bit value.
            let d_1 = self.adv(meta, 1, 1);
            // b_2 has been constrained outside this gate to be a five-bit value.
            let b_2 = self.adv(meta, 2, 1);
            // z13_c is the 13th running sum output by the 10-bit Sinsemilla
            // decomposition of `c`.
            let z13_c = self.adv(meta, 0, 2);
            let b2_c_prime = self.adv(meta, 1, 2);
            let z14_b2_c_prime = self.adv(meta, 2, 2);

            let d1_bool_check = bool_check(d_1.clone());
            // Check that d_whole is consistent with the witnessed subpieces.
            let d_decomposition_check = d_whole - (d_0.clone() + d_1.clone() * two_pow_9);
            // Check that nk = b_2 (5 bits) || c (240 bits) || d_0 (9 bits) || d_1 (1 bit)
            let nk_decomposition_check = b_2.clone()
                + c.clone() * two_pow_5
                + d_0.clone() * two_pow_245
                + d_1.clone() * two_pow_254
                - nk;

            // The `nk` canonicity checks are enforced if and only if `d_1` = 1.
            // d_1 = 1 => d_0 = 0
            let c0_canon_check = d_1.clone() * d_0;
            // d_1 = 1 => z13_c = 0
            let z13_c_check = d_1.clone() * z13_c;
            // Check that b2_c_prime = b_2 + c * 2^5 + 2^140 - t_P.
            // This is checked regardless of the value of d_1.
            let b2_c_prime_check = {
                let two_pow_140 = Expression::Constant(two_pow(B2_C_PRIME_WORDS * 10));
                b_2 + c * two_pow_5 + two_pow_140 - t_p.clone() - b2_c_prime
            };
            // Check that the running sum output by the 140-bit little-endian
            // decomposition of b2_c_prime is zero.
            let z14_b2_c_prime_check = d_1 * z14_b2_c_prime;

            Constraints::with_selector(
                q_commit_ivk_nk,
                [
                    ("d1_bool_check", d1_bool_check),
                    ("d_decomposition_check", d_decomposition_check),
                    ("nk_decomposition_check", nk_decomposition_check),
                    ("c0_canon_check", c0_canon_check),
                    ("z13_c_check", z13_c_check),
                    ("b2_c_prime_check", b2_c_prime_check),
                    ("z14_b2_c_prime", z14_b2_c_prime_check),
                ],
            )
        });
    }

    /// `ivk = Commit^ivk_rivk(ak, nk)`.
    ///
    /// `ak` is an existing cell. `nk` and `rivk` are witnessed here. The
    /// decompositions of `ak` and `nk` are constrained to be canonical.
    ///
    /// `ivk = ⊥` aborts proof creation, as in the Action circuit.
    pub(in crate::circuit::halo2::address_signature) fn commit_ivk(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        ak: &Cell,
        nk: Value<pallas::Base>,
        rivk: Value<pallas::Scalar>,
    ) -> Result<Cell, Error> {
        let ak_value = ak.value().copied();
        let ak_bits = |start, end| ak_value.map(|ak| bit_range(&ak, start, end));
        let nk_bits = |start, end| nk.map(|nk| bit_range(&nk, start, end));

        // a = bits 0..=249 of `ak`
        let a = ak_bits(0, A_BITS);
        // b = b_0 || b_1 || b_2
        //   = (bits 250..=253 of `ak`) || (bit 254 of `ak`) || (bits 0..=4 of `nk`)
        let b_0 = ak_bits(A_BITS, TOP_BIT);
        let b_1 = ak_bits(TOP_BIT, TOP_BIT + 1);
        let b_2 = nk_bits(0, B_2_BITS);
        let b =
            b_0 + b_1 * Value::known(two_pow(B_0_BITS)) + b_2 * Value::known(two_pow(B_0_BITS + 1));
        // c = bits 5..=244 of `nk`
        let c = nk_bits(B_2_BITS, B_2_BITS + C_BITS);
        // d = d_0 || d_1 = (bits 245..=253 of `nk`) || (bit 254 of `nk`)
        let d_0 = nk_bits(B_2_BITS + C_BITS, TOP_BIT);
        let d_1 = nk_bits(TOP_BIT, TOP_BIT + 1);
        let d = d_0 + d_1 * Value::known(two_pow(D_0_BITS));

        // https://p.z.cash/orchard-0.1:commit-ivk-bit-lengths?partial
        let b_0 = self.range_check_short(layouter.namespace(|| "b_0"), b_0, B_0_BITS)?;
        let b_2 = self.range_check_short(layouter.namespace(|| "b_2"), b_2, B_2_BITS)?;
        let d_0 = self.range_check_short(layouter.namespace(|| "d_0"), d_0, D_0_BITS)?;

        // ivk = Commit^ivk_rivk(I2LEBSP_255(ak) || I2LEBSP_255(nk))
        //
        // https://p.z.cash/ZKS:action-addr-integrity?partial
        let pieces = [(a, A_WORDS), (b, B_WORDS), (c, C_WORDS), (d, D_WORDS)]
            .map(|(value, num_words)| Piece { value, num_words });
        let (hash, sums) = self.hash_to_point(
            layouter.namespace(|| "Hash ak||nk"),
            OrchardHashDomains::CommitIvk.Q(),
            &pieces,
        )?;
        let blind = self.mul_fixed(
            layouter.namespace(|| "[rivk] R"),
            &OrchardFixedBasesFull::CommitIvkR,
            rivk,
        )?;
        let commitment = self.add(layouter.namespace(|| "M + [rivk] R"), &hash, &blind)?;
        let ivk = commitment.x;

        // `ak` = `a (250 bits) || b_0 (4 bits) || b_1 (1 bit)`
        // - b_1 = 1 => b_0 = 0
        // - b_1 = 1 => a < t_P
        //     - (0 ≤ a < 2^130) => z13_a of SinsemillaHash(a) == 0
        //     - 0 ≤ a + 2^130 - t_P < 2^130 (thirteen 10-bit lookups)
        //
        // https://p.z.cash/orchard-0.1:commit-ivk-canonicity-ak?partial
        let t_p = pallas::Base::from_u128(T_P);
        let a_prime = self.range_check(
            layouter.namespace(|| "Decompose low 130 bits of (a + 2^130 - t_P)"),
            a.map(|a| a + two_pow(A_PRIME_WORDS * 10) - t_p),
            A_PRIME_WORDS,
        )?;

        // `nk` = `b_2 (5 bits) || c (240 bits) || d_0 (9 bits) || d_1 (1 bit)
        // - d_1 = 1 => d_0 = 0
        // - d_1 = 1 => b_2 + c * 2^5 < t_P
        //      - 0 ≤ b_2 + c * 2^5 < 2^140
        //      - 0 ≤ b_2 + c * 2^5 + 2^140 - t_P < 2^140 (14 ten-bit lookups)
        //
        // https://p.z.cash/orchard-0.1:commit-ivk-canonicity-nk?partial
        let b2_c_prime = self.range_check(
            layouter.namespace(|| "Decompose low 140 bits of (b_2 + c * 2^5 + 2^140 - t_P)"),
            b_2.value().zip(c).map(|(b_2, c)| {
                *b_2 + c * two_pow(B_2_BITS) + two_pow(B2_C_PRIME_WORDS * 10) - t_p
            }),
            B2_C_PRIME_WORDS,
        )?;

        layouter.assign_region(
            || "CommitIvk canonicity of ak",
            |mut region| {
                super::enter("CommitIvk canonicity of ak");
                self.q_commit_ivk_ak.enable(&mut region, 0)?;
                copy(&mut region, ak, self.a[0], 0)?;
                copy(&mut region, &sums[0][0], self.a[1], 0)?;
                copy(&mut region, &sums[1][0], self.a[2], 0)?;
                copy(&mut region, &b_0, self.a[0], 1)?;
                assign(&mut region, self.a[1], 1, b_1)?;
                copy(&mut region, &b_2, self.a[2], 1)?;
                copy(&mut region, &sums[0][Z_13], self.a[0], 2)?;
                copy(&mut region, &a_prime[0], self.a[1], 2)?;
                copy(&mut region, &a_prime[A_PRIME_WORDS], self.a[2], 2)?;
                Ok(())
            },
        )?;
        layouter.assign_region(
            || "CommitIvk canonicity of nk",
            |mut region| {
                super::enter("CommitIvk canonicity of nk");
                self.q_commit_ivk_nk.enable(&mut region, 0)?;
                assign(&mut region, self.a[0], 0, nk)?;
                copy(&mut region, &sums[2][0], self.a[1], 0)?;
                copy(&mut region, &sums[3][0], self.a[2], 0)?;
                copy(&mut region, &d_0, self.a[0], 1)?;
                assign(&mut region, self.a[1], 1, d_1)?;
                copy(&mut region, &b_2, self.a[2], 1)?;
                copy(&mut region, &sums[2][Z_13], self.a[0], 2)?;
                copy(&mut region, &b2_c_prime[0], self.a[1], 2)?;
                copy(&mut region, &b2_c_prime[B2_C_PRIME_WORDS], self.a[2], 2)?;
                Ok(())
            },
        )?;

        Ok(ivk)
    }
}
