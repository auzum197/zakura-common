//! Orchard receive-authority signatures.
//!
//! A receive-authority signature proves that the signer holds the incoming viewing key
//! of an Orchard address. The address is the public key: `pk_d = [ivk] g_d`, so a
//! Schnorr signature on the base `g_d` proves knowledge of `ivk`. There is no circuit.
//!
//! # What a signature proves
//!
//! It proves that the signer can receive and view payments to the Orchard receiver.
//! It does **not** prove ownership or control of the address or of funds. Each holder
//! of the incoming viewing key, full viewing key, or spending key can sign, and there
//! is no revocation. An interface that shows a successful result must say this.
//!
//! A verifier that requires control of funds must use
//! [`spend_authority`](super::spend_authority) and must not fall back to this scheme.

use corez::io::{self, Read, Write};
use rand::CryptoRng;
use zeroize::Zeroize;

use super::{
    CoinType, DIGEST_LENGTH, InvalidTextEncoding, PERSONALIZATION_PREFIX_LENGTH, decode_text,
    encode_text,
};
use crate::backend::pallas;
use crate::backend::prelude::*;
use crate::{
    Address,
    keys::IncomingViewingKey,
    spec::{NonIdentityPallasPoint, NonZeroPallasScalar, to_scalar},
};

/// The signature version that this module implements.
const VERSION: u8 = 1;

/// Length in bytes of the version field.
const VERSION_LENGTH: usize = 1;

/// Length in bytes of an encoded Pallas point or scalar.
const ELEMENT_LENGTH: usize = 32;

/// Length in bytes of the raw encoding of a receive-authority signature:
/// `version || repr(R) || s`.
pub const SIGNATURE_SIZE: usize = VERSION_LENGTH + 2 * ELEMENT_LENGTH;

/// Prefix of the text encoding of a receive-authority signature. It differs from the
/// prefix of a spend-authority signature, so neither parses as the other.
pub const TEXT_PREFIX: &str = "ZOrchRecvSig";

/// ASCII prefix of the message digest personalization.
const DIGEST_PERSONALIZATION_PREFIX: &[u8; PERSONALIZATION_PREFIX_LENGTH] = b"ZOrchRecvSig";

/// BLAKE2b-512 personalization of the hash to scalar `H*`.
const HASH_TO_SCALAR_PERSONALIZATION: &[u8; 16] = b"ZcashRecvSigHash";

/// Output length in bytes of the BLAKE2b-512 hash inside `H*`.
const HASH_TO_SCALAR_LENGTH: usize = 64;

/// Domain separator of the `H*` input that derives the nonce.
const NONCE_DOMAIN: u8 = 0x00;

/// Domain separator of the `H*` input that derives the challenge.
const CHALLENGE_DOMAIN: u8 = 0x01;

/// Length in bytes of the fresh randomness `T` in the nonce derivation.
const NONCE_RANDOMNESS_LENGTH: usize = 32;

/// An error from receive-authority signing or verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The address is not derived from the incoming viewing key.
    AddressNotFromKey,
    /// The signature does not verify for the address, network, and message.
    InvalidSignature,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::AddressNotFromKey => "the address is not derived from the incoming viewing key",
            Self::InvalidSignature => "invalid receive-authority signature",
        })
    }
}

impl core::error::Error for Error {}

/// A version 1 receive-authority signature `(R, s)` for an Orchard address.
///
/// # Invariants
///
/// `R` is a canonical non-identity Pallas point and `s` is a canonical scalar, so each
/// signature has one encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    r: NonIdentityPallasPoint,
    s: pallas::Scalar,
}

/// `H*`: BLAKE2b-512 of the concatenated `parts`, read as a little-endian integer and
/// reduced modulo the Pallas scalar field order.
fn hash_to_scalar(parts: &[&[u8]]) -> pallas::Scalar {
    let mut state = blake2b_simd::Params::new()
        .hash_length(HASH_TO_SCALAR_LENGTH)
        .personal(HASH_TO_SCALAR_PERSONALIZATION)
        .to_state();
    for part in parts {
        state.update(part);
    }
    let mut wide = [0u8; HASH_TO_SCALAR_LENGTH];
    wide.copy_from_slice(state.finalize().as_bytes());
    let scalar = to_scalar(wide);
    wide.zeroize();
    scalar
}

/// The message digest: `BLAKE2b-256("ZOrchRecvSig" || coinType, version || addr || msg)`.
fn message_digest(coin_type: CoinType, address: &Address, message: &[u8]) -> [u8; DIGEST_LENGTH] {
    coin_type.digest(
        DIGEST_PERSONALIZATION_PREFIX,
        &[&[VERSION], &address.to_raw_address_bytes(), message],
    )
}

/// The challenge `c = H*(0x01 || repr(R) || addr || digest)`.
fn challenge(
    r: &NonIdentityPallasPoint,
    address: &Address,
    digest: &[u8; DIGEST_LENGTH],
) -> pallas::Scalar {
    hash_to_scalar(&[
        &[CHALLENGE_DOMAIN],
        &r.to_bytes(),
        &address.to_raw_address_bytes(),
        digest,
    ])
}

impl Signature {
    /// Signs `message` for `address` with the incoming viewing key of the address.
    ///
    /// A holder of a full viewing key or a spending key derives `ivk` first, for the
    /// scope of the address, with [`FullViewingKey::to_ivk`].
    ///
    /// The nonce is derived from fresh randomness, `ivk`, and the message digest. A
    /// caller cannot supply it.
    ///
    /// Returns [`Error::AddressNotFromKey`] if `ivk` does not derive `address`.
    ///
    /// [`FullViewingKey::to_ivk`]: crate::keys::FullViewingKey::to_ivk
    pub fn sign(
        ivk: &IncomingViewingKey,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
        mut rng: impl CryptoRng,
    ) -> Result<Self, Error> {
        if ivk.address(address.diversifier()) != *address {
            return Err(Error::AddressNotFromKey);
        }
        let g_d = address.g_d();
        let ivk = ivk.key_agreement_scalar();
        let digest = message_digest(coin_type, address, message);

        // k = H*(0x00 || T || I2LEOSP_256(ivk) || digest), with a new T if k = 0.
        let mut ivk_bytes = ivk.to_repr();
        let k = loop {
            let mut randomness = [0u8; NONCE_RANDOMNESS_LENGTH];
            rng.fill_bytes(&mut randomness);
            let k = hash_to_scalar(&[&[NONCE_DOMAIN], &randomness, &ivk_bytes, &digest]);
            randomness.zeroize();
            if let Some(k) = NonZeroPallasScalar::from_scalar(k).into_option() {
                break k;
            }
        };
        ivk_bytes.zeroize();

        // R = [k] g_d. This multiplication is constant time. `k` is not zero and
        // `g_d` has prime order, so R is not the identity.
        let r = NonIdentityPallasPoint::expect_non_identity(*g_d * *k);
        let c = challenge(&r, address, &digest);
        // s = k + c * ivk (mod r_P). Field arithmetic is constant time.
        let s = *k + c * **ivk;

        Ok(Signature { r, s })
    }

    /// Verifies that this signature binds `message` to `address` on the network
    /// `coin_type`.
    ///
    /// Success proves that the signer holds the incoming viewing key of the Orchard
    /// receiver. It does not prove control of funds.
    pub fn verify(
        &self,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
    ) -> Result<(), Error> {
        let g_d = address.g_d();
        let digest = message_digest(coin_type, address, message);
        let c = challenge(&self.r, address, &digest);

        // Accept iff [s] g_d = R + [c] pk_d.
        if *g_d * self.s == *self.r + *address.pk_d().inner() * c {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }

    /// Returns the raw encoding `version || repr(R) || I2LEOSP_256(s)`.
    pub fn to_bytes(&self) -> [u8; SIGNATURE_SIZE] {
        let mut bytes = [0u8; SIGNATURE_SIZE];
        let (version, rest) = bytes.split_at_mut(VERSION_LENGTH);
        let (r, s) = rest.split_at_mut(ELEMENT_LENGTH);
        version[0] = VERSION;
        r.copy_from_slice(&self.r.to_bytes());
        s.copy_from_slice(&self.s.to_repr());
        bytes
    }

    /// Parses the raw encoding.
    ///
    /// Returns `None` if the version is unknown, if `R` is not a canonical
    /// non-identity point, or if `s` is not a canonical scalar.
    pub fn from_bytes(bytes: &[u8; SIGNATURE_SIZE]) -> Option<Self> {
        let (version, rest) = bytes.split_at(VERSION_LENGTH);
        let (r, s) = rest.split_at(ELEMENT_LENGTH);
        if version[0] != VERSION {
            return None;
        }
        let r = NonIdentityPallasPoint::from_bytes(r.try_into().expect("R is one element"))
            .into_option()?;
        let s = pallas::Scalar::from_repr(s.try_into().expect("s is one element")).into_option()?;
        Some(Signature { r, s })
    }

    /// Reads the raw encoding.
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut bytes = [0u8; SIGNATURE_SIZE];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid receive-authority signature encoding",
            )
        })
    }

    /// Writes the raw encoding.
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// The text encoding: `ZOrchRecvSig:` and the standard Base64 encoding of the raw encoding.
impl core::fmt::Display for Signature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&encode_text(TEXT_PREFIX, &self.to_bytes()))
    }
}

/// Parses the text encoding.
///
/// Fails if the prefix is not `ZOrchRecvSig:`, if the Base64 text is not canonical, or if the
/// raw encoding is not valid. The text encoding of a spend-authority signature does not
/// parse.
impl core::str::FromStr for Signature {
    type Err = InvalidTextEncoding;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        decode_text(TEXT_PREFIX, text)
            .and_then(|raw| <[u8; SIGNATURE_SIZE]>::try_from(raw).ok())
            .and_then(|raw| Self::from_bytes(&raw))
            .ok_or(InvalidTextEncoding)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use alloc::vec::Vec;

    use proptest::prelude::*;

    use super::{ELEMENT_LENGTH, Error, SIGNATURE_SIZE, Signature, VERSION, VERSION_LENGTH};
    use crate::{
        Address,
        address::testing::arb_address,
        address_signature::{CoinType, testing::arb_coin_type},
        keys::{Diversifier, FullViewingKey, Scope, SpendingKey, testing::arb_spending_key},
        rng_compat::OsRng,
    };

    /// Length in bytes of the raw encoding that the draft ZIP specifies.
    const SPECIFIED_SIGNATURE_SIZE: usize = 65;

    /// Upper bound on the length of a generated message.
    const MAX_MESSAGE_LENGTH: usize = 256;

    /// Spending key bytes of the regression vector.
    const VECTOR_SPENDING_KEY: [u8; 32] = [7; 32];

    /// Diversifier of the regression vector.
    const VECTOR_DIVERSIFIER: [u8; 11] = [3; 11];

    /// Message of the regression vector.
    const VECTOR_MESSAGE: &[u8] = b"Orchard receive-authority signature test vector";

    /// A Mainnet signature by the external incoming viewing key of
    /// [`VECTOR_SPENDING_KEY`], for the address at [`VECTOR_DIVERSIFIER`], on
    /// [`VECTOR_MESSAGE`]. It pins the hash domains and the encoding.
    const VECTOR_SIGNATURE: &str = include_str!("test_vectors/receive_authority_v1.hex");

    fn arb_scope() -> impl Strategy<Value = Scope> {
        prop_oneof![Just(Scope::External), Just(Scope::Internal)]
    }

    fn arb_message() -> impl Strategy<Value = Vec<u8>> {
        prop::collection::vec(any::<u8>(), 0..MAX_MESSAGE_LENGTH)
    }

    prop_compose! {
        /// Generates a spending key with one of its addresses and the scope of the address.
        fn arb_key_and_address()(
            sk in arb_spending_key(),
            d in prop::array::uniform11(any::<u8>()),
            scope in arb_scope(),
        ) -> (SpendingKey, Address, Scope) {
            let address = FullViewingKey::from(&sk).address(Diversifier::from_bytes(d), scope);
            (sk, address, scope)
        }
    }

    fn vector_address() -> (FullViewingKey, Address) {
        let sk = SpendingKey::from_bytes(VECTOR_SPENDING_KEY).unwrap();
        let fvk = FullViewingKey::from(&sk);
        let address = fvk.address(Diversifier::from_bytes(VECTOR_DIVERSIFIER), Scope::External);
        (fvk, address)
    }

    #[test]
    fn encoding_has_the_specified_length() {
        assert_eq!(SIGNATURE_SIZE, SPECIFIED_SIGNATURE_SIZE);
    }

    /// Set `ORCHARD_ADDRESS_SIGNATURE_GENERATE_VECTORS` to regenerate the vector.
    #[test]
    fn regression_vector_verifies() {
        let (fvk, address) = vector_address();
        if std::env::var_os("ORCHARD_ADDRESS_SIGNATURE_GENERATE_VECTORS").is_some() {
            let signature = Signature::sign(
                &fvk.to_ivk(Scope::External),
                &address,
                CoinType::MAINNET,
                VECTOR_MESSAGE,
                OsRng,
            )
            .unwrap();
            std::fs::write(
                "src/address_signature/test_vectors/receive_authority_v1.hex",
                format!("{}\n", hex::encode(signature.to_bytes())),
            )
            .unwrap();
            return;
        }
        let bytes: [u8; SIGNATURE_SIZE] = hex::decode(VECTOR_SIGNATURE.trim())
            .unwrap()
            .try_into()
            .unwrap();
        let signature = Signature::from_bytes(&bytes).unwrap();
        assert_eq!(
            signature.verify(&address, CoinType::MAINNET, VECTOR_MESSAGE),
            Ok(())
        );
        assert_eq!(
            signature.verify(&address, CoinType::TESTNET, VECTOR_MESSAGE),
            Err(Error::InvalidSignature)
        );
    }

    proptest! {
        #[test]
        fn sign_verify_round_trip(
            (sk, address, scope) in arb_key_and_address(),
            coin_type in arb_coin_type(),
            message in arb_message(),
        ) {
            let ivk = FullViewingKey::from(&sk).to_ivk(scope);
            let signature = Signature::sign(&ivk, &address, coin_type, &message, OsRng).unwrap();
            prop_assert_eq!(signature.verify(&address, coin_type, &message), Ok(()));

            let encoded = signature.to_bytes();
            prop_assert_eq!(Signature::from_bytes(&encoded), Some(signature.clone()));
            let mut written = Vec::new();
            signature.write(&mut written).unwrap();
            prop_assert_eq!(&written[..], &encoded[..]);
            prop_assert_eq!(Signature::read(&written[..]).unwrap(), signature.clone());

            // The text encoding round-trips, and has only its own prefix.
            let text = alloc::format!("{signature}");
            prop_assert!(text.starts_with("ZOrchRecvSig:"));
            prop_assert_eq!(text.parse(), Ok(signature));
            let (_, encoded) = text.split_once(':').unwrap();
            for other in [
                alloc::format!("ZOrchAddrSig:{encoded}"),
                encoded.into(),
                alloc::format!("ZOrchRecvSig:{encoded} "),
                alloc::format!("zorchrecvsig:{encoded}"),
            ] {
                prop_assert_eq!(
                    other.parse::<Signature>(),
                    Err(crate::address_signature::InvalidTextEncoding)
                );
            }
        }

        #[test]
        fn rejects_a_different_statement(
            (sk, address, scope) in arb_key_and_address(),
            other_address in arb_address(),
            message in arb_message(),
            other_message in arb_message(),
        ) {
            prop_assume!(address != other_address);
            prop_assume!(message != other_message);
            let fvk = FullViewingKey::from(&sk);
            let ivk = fvk.to_ivk(scope);
            let signature =
                Signature::sign(&ivk, &address, CoinType::MAINNET, &message, OsRng).unwrap();

            let invalid = Err(Error::InvalidSignature);
            prop_assert_eq!(signature.verify(&address, CoinType::MAINNET, &other_message), invalid);
            prop_assert_eq!(signature.verify(&address, CoinType::TESTNET, &message), invalid);
            prop_assert_eq!(signature.verify(&other_address, CoinType::MAINNET, &message), invalid);

            // Another address of the same key: the signature is bound to one address.
            let sibling = fvk.address(other_address.diversifier(), scope);
            prop_assume!(sibling != address);
            prop_assert_eq!(signature.verify(&sibling, CoinType::MAINNET, &message), invalid);
        }

        #[test]
        fn rejects_a_key_that_does_not_derive_the_address(
            (sk, address, scope) in arb_key_and_address(),
            other_sk in arb_spending_key(),
            message in arb_message(),
        ) {
            let other_scope = match scope {
                Scope::External => Scope::Internal,
                Scope::Internal => Scope::External,
            };
            for ivk in [
                FullViewingKey::from(&sk).to_ivk(other_scope),
                FullViewingKey::from(&other_sk).to_ivk(scope),
            ] {
                prop_assert_eq!(
                    Signature::sign(&ivk, &address, CoinType::MAINNET, &message, OsRng),
                    Err(Error::AddressNotFromKey)
                );
            }
        }

        #[test]
        fn rejects_tampered_encodings(
            (sk, address, scope) in arb_key_and_address(),
            message in arb_message(),
            index in 0..SIGNATURE_SIZE,
            bit in 0..u8::BITS,
        ) {
            let ivk = FullViewingKey::from(&sk).to_ivk(scope);
            let signature =
                Signature::sign(&ivk, &address, CoinType::MAINNET, &message, OsRng).unwrap();
            let mut encoded = signature.to_bytes();
            encoded[index] ^= 1 << bit;

            // A changed encoding does not parse, or it does not verify.
            let accepted = Signature::from_bytes(&encoded)
                .is_some_and(|tampered| {
                    tampered.verify(&address, CoinType::MAINNET, &message).is_ok()
                });
            prop_assert!(!accepted);
        }

        #[test]
        fn signatures_are_randomized(
            (sk, address, scope) in arb_key_and_address(),
            message in arb_message(),
        ) {
            let ivk = FullViewingKey::from(&sk).to_ivk(scope);
            let sign = || Signature::sign(&ivk, &address, CoinType::MAINNET, &message, OsRng);
            prop_assert_ne!(sign().unwrap(), sign().unwrap());
        }
    }

    #[test]
    fn rejects_non_canonical_encodings() {
        let (fvk, address) = vector_address();
        let signature = Signature::sign(
            &fvk.to_ivk(Scope::External),
            &address,
            CoinType::MAINNET,
            VECTOR_MESSAGE,
            OsRng,
        )
        .unwrap();
        let encoded = signature.to_bytes();
        let r = VERSION_LENGTH..VERSION_LENGTH + ELEMENT_LENGTH;
        let s = r.end..SIGNATURE_SIZE;

        // An unknown version.
        let mut unknown_version = encoded;
        unknown_version[0] = VERSION + 1;
        assert_eq!(Signature::from_bytes(&unknown_version), None);

        // The identity as R. Its encoding is all zeroes.
        let mut identity_r = encoded;
        identity_r[r].fill(0);
        assert_eq!(Signature::from_bytes(&identity_r), None);

        // s is not less than the scalar field order.
        let mut large_s = encoded;
        large_s[s].fill(u8::MAX);
        assert_eq!(Signature::from_bytes(&large_s), None);
    }
}
