//! Orchard address signatures, which prove control of spend authority.
//!
//! A signature is `(version, rk, σ, π)`:
//!
//! - `rk` is a fresh randomization of the spend validating key behind the address.
//! - `π` is a Halo 2 proof of the Address signature statement: `rk` is a randomization
//!   of the key `ak` that, with `nk` and `rivk`, derives the address `(g_d, pk_d)`.
//! - `σ` is a RedPallas signature under `rk` on a digest of the version, network,
//!   address, `rk`, `π`, and the message.
//!
//! A full viewing key holder can make `π` but cannot make `σ`. An incoming viewing key
//! holder cannot make `π`.
//!
//! # What a signature proves
//!
//! It proves control of spend authority for the Orchard receiver. For a Unified
//! Address it says nothing about the other receivers, and an interface that shows a
//! successful result must say so. It does not prove ownership of notes or funds.
//!
//! # Signing
//!
//! [`AddressSignature::sign`] does all steps. [`UnsignedAddressSignature`] splits them:
//! [`UnsignedAddressSignature::prove`] needs only the full viewing key, and
//! [`UnsignedAddressSignature::sign`] needs only the spend authorizing key. The signer
//! computes the digest itself from the address and message it was given. There is no
//! interface that signs a caller-supplied digest.

use alloc::vec::Vec;

use corez::io::{self, Read, Write};
#[cfg(feature = "prover")]
use rand::CryptoRng;

use super::{
    CoinType, DIGEST_LENGTH, InvalidTextEncoding, PERSONALIZATION_PREFIX_LENGTH, decode_text,
    encode_text,
};
use crate::{
    Address,
    circuit::address_signature as circuit,
    primitives::redpallas::{self, SpendAuth, VerificationKey},
};
#[cfg(feature = "prover")]
use crate::{
    keys::{FullViewingKey, SpendAuthorizingKey, SpendValidatingKey},
    primitives::redpallas::SpendAuthRandomizer,
};

pub use circuit::{ProvingKey, VerifyingKey};

/// The signature version that this module implements.
const VERSION: u8 = 1;

/// Length in bytes of the version field.
const VERSION_LENGTH: usize = 1;

/// Length in bytes of an encoded `rk`.
const RK_LENGTH: usize = 32;

/// Length in bytes of an encoded RedPallas signature.
const SPEND_AUTH_SIG_LENGTH: usize = 64;

/// Length in bytes of a version 1 proof, `ℓ_π`. The circuit determines it.
pub const PROOF_SIZE: usize = 2784;

/// Length in bytes of the raw encoding of a version 1 address signature:
/// `version || repr(rk) || σ || π`.
pub const SIGNATURE_SIZE: usize = VERSION_LENGTH + RK_LENGTH + SPEND_AUTH_SIG_LENGTH + PROOF_SIZE;

/// Prefix of the text encoding of an address signature. It is the same string as
/// the start of the digest personalization. It differs from the prefix of a
/// receive-authority signature, so neither parses as the other.
pub const TEXT_PREFIX: &str = "ZOrchAddrSig";

/// ASCII prefix of the message digest personalization.
const DIGEST_PERSONALIZATION_PREFIX: &[u8; PERSONALIZATION_PREFIX_LENGTH] = b"ZOrchAddrSig";

/// An error from address signature creation or verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The address is not derived from the full viewing key, in either scope.
    AddressNotFromKey,
    /// The spend authorizing key does not correspond to the full viewing key, or to
    /// the `rk` of the unsigned signature.
    KeyMismatch,
    /// The prover failed an internal check. This indicates a bug, not bad input.
    ProvingFailed,
    /// The RedPallas signature does not verify under `rk` for the address, network,
    /// and message.
    InvalidSignature,
    /// The proof does not verify for the address and `rk`.
    InvalidProof,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::AddressNotFromKey => "the address is not derived from the full viewing key",
            Self::KeyMismatch => "the spend authorizing key does not match",
            Self::ProvingFailed => "internal proof invariant failed",
            Self::InvalidSignature => "invalid spend authorization signature",
            Self::InvalidProof => "invalid address signature proof",
        })
    }
}

impl core::error::Error for Error {}

/// `BLAKE2b-256("ZOrchAddrSig" || coinType, version || addr || repr(rk) || π || msg)`.
///
/// The proof has a fixed length for the version, so the input parses in one way only.
fn message_digest(
    coin_type: CoinType,
    address: &Address,
    rk: &VerificationKey<SpendAuth>,
    proof: &[u8],
    message: &[u8],
) -> [u8; DIGEST_LENGTH] {
    debug_assert_eq!(proof.len(), PROOF_SIZE);
    coin_type.digest(
        DIGEST_PERSONALIZATION_PREFIX,
        &[
            &[VERSION],
            &address.to_raw_address_bytes(),
            &<[u8; RK_LENGTH]>::from(rk),
            proof,
            message,
        ],
    )
}

/// BLAKE2b-512 personalization of the hedged nonce bytes.
#[cfg(feature = "prover")]
const NONCE_PERSONALIZATION: &[u8; 16] = b"ZOrchAddrSigNonc";

/// Length in bytes of the fresh randomness `T` in the hedged nonce bytes.
#[cfg(feature = "prover")]
const NONCE_RANDOMNESS_LENGTH: usize = 32;

/// Length in bytes of one block of hedged nonce bytes: a BLAKE2b-512 output.
#[cfg(feature = "prover")]
const NONCE_BLOCK_LENGTH: usize = 64;

/// The source of the random bytes of RedPallas signing.
///
/// RedPallas signing derives its nonce from random bytes, the verification key, and
/// the message. It does not use the signing key. If the random bytes are
/// predictable, one signature reveals the key. This source gives the bytes
///
/// `BLAKE2b-512("ZOrchAddrSigNonc", i || rsk || T || digest)` for `i = 0, 1, ...`
///
/// where `i` is one byte and `T` is fresh randomness. The bytes are unpredictable if
/// `T` is, and also if `T` is not but the key is secret.
#[cfg(feature = "prover")]
struct HedgedNonceSource {
    rsk: [u8; RK_LENGTH],
    randomness: [u8; NONCE_RANDOMNESS_LENGTH],
    digest: [u8; DIGEST_LENGTH],
    block: [u8; NONCE_BLOCK_LENGTH],
    /// Index of the next block.
    next_block: u8,
    /// Number of bytes of `block` that were given out.
    used: usize,
}

#[cfg(feature = "prover")]
impl HedgedNonceSource {
    fn new(
        rsk: &redpallas::SigningKey<SpendAuth>,
        randomness: [u8; NONCE_RANDOMNESS_LENGTH],
        digest: &[u8; DIGEST_LENGTH],
    ) -> Self {
        HedgedNonceSource {
            rsk: rsk.into(),
            randomness,
            digest: *digest,
            block: [0; NONCE_BLOCK_LENGTH],
            next_block: 0,
            used: NONCE_BLOCK_LENGTH,
        }
    }

    fn fill(&mut self, dest: &mut [u8]) {
        for byte in dest {
            if self.used == NONCE_BLOCK_LENGTH {
                let hash = blake2b_simd::Params::new()
                    .hash_length(NONCE_BLOCK_LENGTH)
                    .personal(NONCE_PERSONALIZATION)
                    .to_state()
                    .update(&[self.next_block])
                    .update(&self.rsk)
                    .update(&self.randomness)
                    .update(&self.digest)
                    .finalize();
                self.block.copy_from_slice(hash.as_bytes());
                self.next_block = self
                    .next_block
                    .checked_add(1)
                    .expect("signing uses less than 256 blocks");
                self.used = 0;
            }
            *byte = self.block[self.used];
            self.used += 1;
        }
    }
}

#[cfg(feature = "prover")]
impl Drop for HedgedNonceSource {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.rsk.zeroize();
        self.randomness.zeroize();
        self.block.zeroize();
    }
}

#[cfg(feature = "prover")]
impl rand::TryRng for HedgedNonceSource {
    type Error = core::convert::Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut bytes = [0u8; 4];
        self.fill(&mut bytes);
        Ok(u32::from_le_bytes(bytes))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut bytes = [0u8; 8];
        self.fill(&mut bytes);
        Ok(u64::from_le_bytes(bytes))
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        self.fill(dest);
        Ok(())
    }
}

#[cfg(feature = "prover")]
impl rand::TryCryptoRng for HedgedNonceSource {}

/// A version 1 address signature `(rk, σ, π)`.
///
/// # Invariants
///
/// `rk` is a canonical non-identity Pallas point, and `π` is [`PROOF_SIZE`] bytes long.
#[derive(Clone, Debug)]
pub struct AddressSignature {
    rk: VerificationKey<SpendAuth>,
    signature: redpallas::Signature<SpendAuth>,
    proof: Vec<u8>,
}

impl AddressSignature {
    /// Signs `message` for `address`.
    ///
    /// `fvk` must be the full viewing key of `ask`, and `address` must be an address
    /// of `fvk` in the external or the internal scope. The randomizer `α` is sampled
    /// from `rng` for each signature. A caller cannot supply it.
    ///
    /// Returns [`Error::KeyMismatch`] if `ask` does not correspond to `fvk`, and
    /// [`Error::AddressNotFromKey`] if `fvk` does not derive `address`.
    #[cfg(feature = "prover")]
    #[cfg_attr(docsrs, doc(cfg(feature = "prover")))]
    pub fn sign(
        pk: &ProvingKey,
        ask: &SpendAuthorizingKey,
        fvk: &FullViewingKey,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
        mut rng: impl CryptoRng,
    ) -> Result<Self, Error> {
        // Do the cheap key check before the proof.
        if SpendValidatingKey::from(ask) != SpendValidatingKey::from(fvk.clone()) {
            return Err(Error::KeyMismatch);
        }
        UnsignedAddressSignature::prove(pk, fvk, address, coin_type, message, &mut rng)?
            .sign(ask, fvk, &mut rng)
    }

    /// Verifies that this signature binds `message` to `address` on the network
    /// `coin_type`.
    ///
    /// Success proves control of spend authority for the Orchard receiver.
    ///
    /// Returns [`Error::InvalidSignature`] if the RedPallas signature is not valid, and
    /// [`Error::InvalidProof`] if the proof is not valid. The signature is checked
    /// first because that check is cheaper.
    #[cfg(feature = "verifier")]
    #[cfg_attr(docsrs, doc(cfg(feature = "verifier")))]
    pub fn verify(
        &self,
        vk: &VerifyingKey,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
    ) -> Result<(), Error> {
        let digest = message_digest(coin_type, address, &self.rk, &self.proof, message);
        self.rk
            .verify(&digest, &self.signature)
            .map_err(|_| Error::InvalidSignature)?;

        let instance = circuit::Instance::new(address, &self.rk).ok_or(Error::InvalidProof)?;
        circuit::verify_proof(vk, &instance, &self.proof).map_err(|_| Error::InvalidProof)
    }

    /// Returns the raw encoding `version || repr(rk) || σ || π`. It is
    /// [`SIGNATURE_SIZE`] bytes long.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(SIGNATURE_SIZE);
        bytes.push(VERSION);
        bytes.extend_from_slice(&<[u8; RK_LENGTH]>::from(&self.rk));
        bytes.extend_from_slice(&<[u8; SPEND_AUTH_SIG_LENGTH]>::from(&self.signature));
        bytes.extend_from_slice(&self.proof);
        bytes
    }

    /// Parses the raw encoding.
    ///
    /// Returns `None` if the version is unknown, or if `rk` is not a canonical
    /// non-identity point. The array type fixes the length.
    pub fn from_bytes(bytes: &[u8; SIGNATURE_SIZE]) -> Option<Self> {
        let (version, rest) = bytes.split_at(VERSION_LENGTH);
        let (rk, rest) = rest.split_at(RK_LENGTH);
        let (signature, proof) = rest.split_at(SPEND_AUTH_SIG_LENGTH);
        if version[0] != VERSION {
            return None;
        }
        let rk: [u8; RK_LENGTH] = rk.try_into().expect("rk is 32 bytes");
        let rk = VerificationKey::<SpendAuth>::try_from(rk).ok()?;
        if rk.is_identity() {
            return None;
        }
        let signature: [u8; SPEND_AUTH_SIG_LENGTH] =
            signature.try_into().expect("the signature is 64 bytes");
        Some(AddressSignature {
            rk,
            signature: signature.into(),
            proof: proof.to_vec(),
        })
    }

    /// Reads the raw encoding.
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut bytes = [0u8; SIGNATURE_SIZE];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid address signature encoding",
            )
        })
    }

    /// Writes the raw encoding.
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// An address signature that has its proof but not yet its RedPallas signature.
///
/// The prover makes this value with the full viewing key. The holder of the spend
/// authorizing key completes it with [`UnsignedAddressSignature::sign`]. A signing
/// device should show [`message`](Self::message) and [`address`](Self::address) to the
/// user before it signs.
///
/// This value contains the randomizer `α`. Together with `rk`, `α` reveals the spend
/// validating key, which links all addresses of the wallet. Give this value only to
/// the signer.
#[cfg(feature = "prover")]
#[cfg_attr(docsrs, doc(cfg(feature = "prover")))]
#[derive(Clone)]
pub struct UnsignedAddressSignature {
    address: Address,
    coin_type: CoinType,
    message: Vec<u8>,
    alpha: SpendAuthRandomizer,
    rk: VerificationKey<SpendAuth>,
    proof: Vec<u8>,
}

#[cfg(feature = "prover")]
impl core::fmt::Debug for UnsignedAddressSignature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnsignedAddressSignature")
            .field("address", &self.address)
            .field("coin_type", &self.coin_type)
            .field("message", &self.message)
            .field("rk", &self.rk)
            .finish_non_exhaustive()
    }
}

#[cfg(feature = "prover")]
impl UnsignedAddressSignature {
    /// Samples a fresh randomizer `α`, computes `rk`, and proves the Address signature
    /// statement. This needs the full viewing key only.
    ///
    /// Returns [`Error::AddressNotFromKey`] if `fvk` does not derive `address` in
    /// either scope.
    pub fn prove(
        pk: &ProvingKey,
        fvk: &FullViewingKey,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
        mut rng: impl CryptoRng,
    ) -> Result<Self, Error> {
        let scope = fvk
            .scope_for_address(address)
            .ok_or(Error::AddressNotFromKey)?;
        let ak = SpendValidatingKey::from(fvk.clone());

        // rk is the identity with negligible probability. The statement and the
        // verifier do not allow it, so sample again.
        let (alpha, rk, instance) = loop {
            let alpha = SpendAuthRandomizer::random(&mut rng);
            let rk = ak.randomize(&alpha);
            if let Some(instance) = circuit::Instance::new(address, &rk) {
                break (alpha, rk, instance);
            }
        };

        let circuit = circuit::Circuit::new(address, ak, alpha, *fvk.nk(), fvk.rivk(scope));
        let proof = circuit::create_proof(pk, circuit, &instance, &mut rng)
            .map_err(|_| Error::ProvingFailed)?;
        if proof.len() != PROOF_SIZE {
            return Err(Error::ProvingFailed);
        }

        Ok(UnsignedAddressSignature {
            address: *address,
            coin_type,
            message: message.to_vec(),
            alpha,
            rk,
            proof,
        })
    }

    /// The address that the signature is for.
    pub fn address(&self) -> &Address {
        &self.address
    }

    /// The network that the signature is for.
    pub fn coin_type(&self) -> CoinType {
        self.coin_type
    }

    /// The message that the signature is for.
    pub fn message(&self) -> &[u8] {
        &self.message
    }

    fn digest(&self) -> [u8; DIGEST_LENGTH] {
        message_digest(
            self.coin_type,
            &self.address,
            &self.rk,
            &self.proof,
            &self.message,
        )
    }

    /// Signs the digest of this value's own fields with the randomized key
    /// `rsk = ask + α`.
    ///
    /// The signer recomputes `rk` from `α` and its own key, and recomputes the digest.
    /// It also checks that the address is an address of its own full viewing key.
    ///
    /// The address check is necessary. This value comes from a prover that the signer
    /// does not trust. A prover can make the proof for a related key
    /// `ak' = ak + [δ] G` and give the randomizer `α + δ`. The `rk` is then correct
    /// for the signer's key, and without the address check the signer would sign for
    /// an address that is not in its wallet.
    ///
    /// The signing nonce is hedged: the random bytes that RedPallas signing uses are
    /// derived from `rsk`, fresh randomness from `rng`, and the digest. A weak random
    /// number generator alone thus does not reveal the key.
    ///
    /// Returns [`Error::KeyMismatch`] if `ask` does not correspond to `fvk`, or if
    /// `ask` randomized by `α` is not `rk`. Returns [`Error::AddressNotFromKey`] if
    /// `fvk` does not derive the address.
    pub fn sign(
        self,
        ask: &SpendAuthorizingKey,
        fvk: &FullViewingKey,
        mut rng: impl CryptoRng,
    ) -> Result<AddressSignature, Error> {
        let ak = SpendValidatingKey::from(ask);
        if ak != SpendValidatingKey::from(fvk.clone()) || ak.randomize(&self.alpha) != self.rk {
            return Err(Error::KeyMismatch);
        }
        if fvk.scope_for_address(&self.address).is_none() {
            return Err(Error::AddressNotFromKey);
        }
        let rsk = ask.randomize(&self.alpha);
        let digest = self.digest();
        let mut randomness = [0u8; NONCE_RANDOMNESS_LENGTH];
        rng.fill_bytes(&mut randomness);
        let signature = rsk.sign(HedgedNonceSource::new(&rsk, randomness, &digest), &digest);
        Ok(AddressSignature {
            rk: self.rk,
            signature,
            proof: self.proof,
        })
    }
}

/// The text encoding: `ZOrchAddrSig:` and the standard Base64 encoding of the raw encoding.
impl core::fmt::Display for AddressSignature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&encode_text(TEXT_PREFIX, &self.to_bytes()))
    }
}

/// Parses the text encoding.
///
/// Fails if the prefix is not `ZOrchAddrSig:`, if the Base64 text is not canonical, or if the
/// raw encoding is not valid. The text encoding of a receive-authority signature does not
/// parse.
impl core::str::FromStr for AddressSignature {
    type Err = InvalidTextEncoding;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        decode_text(TEXT_PREFIX, text)
            .and_then(|raw| <[u8; SIGNATURE_SIZE]>::try_from(raw).ok())
            .and_then(|raw| Self::from_bytes(&raw))
            .ok_or(InvalidTextEncoding)
    }
}

#[cfg(all(test, feature = "prover", feature = "verifier"))]
mod tests {
    use alloc::vec::Vec;
    use std::sync::OnceLock;

    use proptest::prelude::*;

    use super::{
        AddressSignature, Error, PROOF_SIZE, ProvingKey, RK_LENGTH, SIGNATURE_SIZE,
        SPEND_AUTH_SIG_LENGTH, UnsignedAddressSignature, VERSION, VERSION_LENGTH, VerifyingKey,
    };
    use crate::{
        Address,
        address::testing::arb_address,
        address_signature::{CoinType, testing::arb_coin_type},
        keys::{
            Diversifier, FullViewingKey, Scope, SpendAuthorizingKey, SpendingKey,
            testing::arb_spending_key,
        },
        rng_compat::OsRng,
    };

    /// Number of proptest cases. Each case creates at least one proof.
    const CASES: u32 = 3;

    /// Upper bound on the length of a generated message.
    const MAX_MESSAGE_LENGTH: usize = 256;

    /// Length in bytes of the fixed part of the encoding that the draft ZIP specifies:
    /// the raw encoding is `97 + ℓ_π` bytes long.
    const SPECIFIED_FIXED_LENGTH: usize = 97;

    /// Size in bytes of a single-Action Orchard proof, which a signature that reuses
    /// the Action circuit would contain.
    const SINGLE_ACTION_PROOF_SIZE: usize = 4992;

    /// Spending key bytes of the regression vector.
    const VECTOR_SPENDING_KEY: [u8; 32] = [7; 32];

    /// Diversifier of the regression vector.
    const VECTOR_DIVERSIFIER: [u8; 11] = [3; 11];

    /// Message of the regression vector.
    const VECTOR_MESSAGE: &[u8] = b"Orchard address signature test vector";

    /// A Mainnet signature by [`VECTOR_SPENDING_KEY`] for its external address at
    /// [`VECTOR_DIVERSIFIER`], on [`VECTOR_MESSAGE`]. It pins the digest, the
    /// encoding, and the verifying key.
    const VECTOR_SIGNATURE: &[u8] = include_bytes!("test_vectors/spend_authority_v1.bin");

    fn proving_key() -> &'static ProvingKey {
        static KEY: OnceLock<ProvingKey> = OnceLock::new();
        KEY.get_or_init(ProvingKey::build)
    }

    fn verifying_key() -> &'static VerifyingKey {
        static KEY: OnceLock<VerifyingKey> = OnceLock::new();
        KEY.get_or_init(VerifyingKey::build)
    }

    fn arb_scope() -> impl Strategy<Value = Scope> {
        prop_oneof![Just(Scope::External), Just(Scope::Internal)]
    }

    fn arb_message() -> impl Strategy<Value = Vec<u8>> {
        prop::collection::vec(any::<u8>(), 0..MAX_MESSAGE_LENGTH)
    }

    prop_compose! {
        /// Generates a spending key with one of its addresses.
        fn arb_key_and_address()(
            sk in arb_spending_key(),
            d in prop::array::uniform11(any::<u8>()),
            scope in arb_scope(),
        ) -> (SpendingKey, Address) {
            let address = FullViewingKey::from(&sk).address(Diversifier::from_bytes(d), scope);
            (sk, address)
        }
    }

    fn sign(
        sk: &SpendingKey,
        address: &Address,
        coin_type: CoinType,
        message: &[u8],
    ) -> Result<AddressSignature, Error> {
        AddressSignature::sign(
            proving_key(),
            &SpendAuthorizingKey::from(sk),
            &FullViewingKey::from(sk),
            address,
            coin_type,
            message,
            OsRng,
        )
    }

    fn encode(signature: &AddressSignature) -> [u8; SIGNATURE_SIZE] {
        signature
            .to_bytes()
            .try_into()
            .expect("the encoding has a fixed length")
    }

    fn vector_address() -> (SpendingKey, Address) {
        let sk = SpendingKey::from_bytes(VECTOR_SPENDING_KEY).unwrap();
        let address = FullViewingKey::from(&sk)
            .address(Diversifier::from_bytes(VECTOR_DIVERSIFIER), Scope::External);
        (sk, address)
    }

    #[test]
    fn encoding_has_the_specified_length() {
        assert_eq!(SIGNATURE_SIZE, SPECIFIED_FIXED_LENGTH + PROOF_SIZE);
        const { assert!(PROOF_SIZE < SINGLE_ACTION_PROOF_SIZE) };
    }

    #[test]
    fn proving_and_verifying_keys_agree() {
        assert_eq!(
            proving_key().verifying_key().fingerprint(),
            verifying_key().fingerprint()
        );
    }

    /// Set `ORCHARD_ADDRESS_SIGNATURE_GENERATE_VECTORS` to regenerate the vector.
    #[test]
    fn regression_vector_verifies() {
        let (sk, address) = vector_address();
        if std::env::var_os("ORCHARD_ADDRESS_SIGNATURE_GENERATE_VECTORS").is_some() {
            let signature = sign(&sk, &address, CoinType::MAINNET, VECTOR_MESSAGE).unwrap();
            std::fs::write(
                "src/address_signature/test_vectors/spend_authority_v1.bin",
                signature.to_bytes(),
            )
            .unwrap();
            return;
        }
        let bytes: &[u8; SIGNATURE_SIZE] = VECTOR_SIGNATURE.try_into().unwrap();
        let signature = AddressSignature::from_bytes(bytes).unwrap();
        assert_eq!(
            signature.verify(verifying_key(), &address, CoinType::MAINNET, VECTOR_MESSAGE),
            Ok(())
        );
        assert_eq!(
            signature.verify(verifying_key(), &address, CoinType::TESTNET, VECTOR_MESSAGE),
            Err(Error::InvalidSignature)
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(CASES))]

        #[test]
        fn sign_verify_round_trip(
            (sk, address) in arb_key_and_address(),
            other_address in arb_address(),
            coin_type in arb_coin_type(),
            message in arb_message(),
            other_message in arb_message(),
        ) {
            prop_assume!(address != other_address);
            prop_assume!(message != other_message);
            let vk = verifying_key();
            let signature = sign(&sk, &address, coin_type, &message).unwrap();
            prop_assert_eq!(signature.verify(vk, &address, coin_type, &message), Ok(()));

            // The encoding round-trips and has the fixed length.
            let encoded = encode(&signature);
            let decoded = AddressSignature::from_bytes(&encoded).unwrap();
            prop_assert_eq!(decoded.to_bytes(), encoded.to_vec());
            prop_assert_eq!(decoded.verify(vk, &address, coin_type, &message), Ok(()));
            let read = AddressSignature::read(&encoded[..]).unwrap();
            prop_assert_eq!(read.to_bytes(), encoded.to_vec());

            // The text encoding round-trips, and has only its own prefix.
            let text = alloc::format!("{signature}");
            prop_assert!(text.starts_with("ZOrchAddrSig:"));
            let from_text: AddressSignature = text.parse().unwrap();
            prop_assert_eq!(from_text.to_bytes(), encoded.to_vec());
            let (_, base64) = text.split_once(':').unwrap();
            for other in [
                alloc::format!("ZOrchRecvSig:{base64}"),
                base64.into(),
                alloc::format!("ZOrchAddrSig:{base64} "),
                alloc::format!("zorchaddrsig:{base64}"),
            ] {
                prop_assert_eq!(
                    other.parse::<AddressSignature>().err(),
                    Some(crate::address_signature::InvalidTextEncoding)
                );
            }

            // A different message, network, or address changes the digest.
            let other_coin_type = if coin_type == CoinType::MAINNET {
                CoinType::TESTNET
            } else {
                CoinType::MAINNET
            };
            let invalid = Err(Error::InvalidSignature);
            prop_assert_eq!(signature.verify(vk, &address, coin_type, &other_message), invalid);
            prop_assert_eq!(signature.verify(vk, &address, other_coin_type, &message), invalid);
            prop_assert_eq!(signature.verify(vk, &other_address, coin_type, &message), invalid);
        }

        #[test]
        fn rejects_tampered_encodings(
            (sk, address) in arb_key_and_address(),
            message in arb_message(),
            index in 0..SIGNATURE_SIZE,
            bit in 0..u8::BITS,
        ) {
            let signature = sign(&sk, &address, CoinType::MAINNET, &message).unwrap();
            let mut encoded = encode(&signature);
            encoded[index] ^= 1 << bit;

            // A changed encoding does not parse, or it does not verify.
            let accepted = AddressSignature::from_bytes(&encoded).is_some_and(|tampered| {
                tampered
                    .verify(verifying_key(), &address, CoinType::MAINNET, &message)
                    .is_ok()
            });
            prop_assert!(!accepted);
        }

        #[test]
        fn a_full_viewing_key_holder_cannot_sign(
            (sk, address) in arb_key_and_address(),
            attacker_sk in arb_spending_key(),
            message in arb_message(),
        ) {
            let fvk = FullViewingKey::from(&sk);
            let attacker_ask = SpendAuthorizingKey::from(&attacker_sk);

            // The one-shot path refuses a key that is not the key of the viewing key.
            let one_shot = AddressSignature::sign(
                proving_key(), &attacker_ask, &fvk, &address, CoinType::MAINNET, &message, OsRng,
            );
            prop_assert_eq!(one_shot.err(), Some(Error::KeyMismatch));

            // The viewing key makes the proof, but only the spend key completes it.
            let unsigned = UnsignedAddressSignature::prove(
                proving_key(), &fvk, &address, CoinType::MAINNET, &message, OsRng,
            ).unwrap();
            prop_assert_eq!(unsigned.address(), &address);
            prop_assert_eq!(unsigned.message(), &message[..]);
            prop_assert_eq!(
                unsigned.clone().sign(&attacker_ask, &fvk, OsRng).err(),
                Some(Error::KeyMismatch)
            );
            let signature = unsigned.sign(&SpendAuthorizingKey::from(&sk), &fvk, OsRng).unwrap();
            prop_assert_eq!(
                signature.verify(verifying_key(), &address, CoinType::MAINNET, &message),
                Ok(())
            );

            // A proof for the attacker's own key does not verify for this address.
            let attacker_fvk = FullViewingKey::from(&attacker_sk);
            let attacker_address = attacker_fvk.address(address.diversifier(), Scope::External);
            let mut forged = sign(&attacker_sk, &attacker_address, CoinType::MAINNET, &message)
                .unwrap();
            prop_assert_eq!(
                forged.verify(verifying_key(), &address, CoinType::MAINNET, &message),
                Err(Error::InvalidSignature)
            );
            // With a valid RedPallas signature under the attacker's rk for the victim
            // address, the proof is what fails.
            let unsigned = UnsignedAddressSignature::prove(
                proving_key(), &attacker_fvk, &attacker_address, CoinType::MAINNET, &message,
                OsRng,
            ).unwrap();
            let rsk = attacker_ask.randomize(&unsigned.alpha);
            forged.rk = unsigned.rk.clone();
            forged.proof = unsigned.proof.clone();
            let digest_for_victim = super::message_digest(
                CoinType::MAINNET, &address, &forged.rk, &forged.proof, &message,
            );
            forged.signature = rsk.sign(OsRng, &digest_for_victim);
            prop_assert_eq!(
                forged.verify(verifying_key(), &address, CoinType::MAINNET, &message),
                Err(Error::InvalidProof)
            );
        }

        #[test]
        fn rejects_an_address_of_another_key(
            sk in arb_spending_key(),
            other_address in arb_address(),
            message in arb_message(),
        ) {
            prop_assume!(FullViewingKey::from(&sk).scope_for_address(&other_address).is_none());
            prop_assert_eq!(
                sign(&sk, &other_address, CoinType::MAINNET, &message).err(),
                Some(Error::AddressNotFromKey)
            );
        }
    }

    /// A prover makes the proof for the related key `ak' = ak + [δ] G`, and gives the
    /// signer the randomizer `α + δ`. The `rk` is then the signer's key randomized by
    /// that randomizer, but the address is not an address of the signer.
    #[test]
    fn signer_refuses_an_address_of_a_related_key() {
        use crate::backend::pallas;
        use crate::backend::prelude::*;
        use crate::constants::fixed_bases::spend_auth_g;
        use crate::keys::SpendValidatingKey;
        use crate::primitives::redpallas::SpendAuthRandomizer;

        /// Offset of `ak` in the raw encoding of a full viewing key.
        const AK_LENGTH: usize = 32;

        let (sk, _) = vector_address();
        let ask = SpendAuthorizingKey::from(&sk);
        let fvk = FullViewingKey::from(&sk);
        let ak = SpendValidatingKey::from(&ask);

        // The first δ for which ak' is a valid spend validating key.
        let generator = spend_auth_g::generator().to_curve();
        let (delta, related_fvk) = (1u64..)
            .find_map(|delta| {
                let delta = pallas::Scalar::from(delta);
                let related_ak = (ak.to_point() + generator * delta).to_bytes();
                let mut bytes = fvk.to_bytes();
                bytes[..AK_LENGTH].copy_from_slice(&related_ak);
                FullViewingKey::from_bytes(&bytes).map(|fvk| (delta, fvk))
            })
            .unwrap();
        let related_address =
            related_fvk.address(Diversifier::from_bytes(VECTOR_DIVERSIFIER), Scope::External);
        assert!(fvk.scope_for_address(&related_address).is_none());

        let mut unsigned = UnsignedAddressSignature::prove(
            proving_key(),
            &related_fvk,
            &related_address,
            CoinType::MAINNET,
            VECTOR_MESSAGE,
            OsRng,
        )
        .unwrap();
        unsigned.alpha = SpendAuthRandomizer::from_scalar(unsigned.alpha.scalar() + delta);

        // The rk check alone does not detect the attack.
        assert_eq!(ak.randomize(&unsigned.alpha), unsigned.rk);
        assert_eq!(
            unsigned.sign(&ask, &fvk, OsRng).err(),
            Some(Error::AddressNotFromKey)
        );
    }

    /// A random number generator that always gives zero bytes.
    struct ZeroRng;

    impl rand::TryRng for ZeroRng {
        type Error = core::convert::Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            Ok(0)
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            Ok(0)
        }

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
            dest.fill(0);
            Ok(())
        }
    }

    impl rand::TryCryptoRng for ZeroRng {}

    /// With a random number generator that has no entropy, the signing nonce still
    /// depends on the key and on the digest.
    #[test]
    fn signing_nonce_is_hedged() {
        /// Length in bytes of the nonce commitment `R` at the start of a RedPallas
        /// signature.
        const R_LENGTH: usize = 32;

        let (sk, address) = vector_address();
        let ask = SpendAuthorizingKey::from(&sk);
        let fvk = FullViewingKey::from(&sk);
        let prove = |message: &[u8]| {
            UnsignedAddressSignature::prove(
                proving_key(),
                &fvk,
                &address,
                CoinType::MAINNET,
                message,
                OsRng,
            )
            .unwrap()
        };
        let nonce_commitment = |signature: &AddressSignature| {
            <[u8; SPEND_AUTH_SIG_LENGTH]>::from(&signature.signature)[..R_LENGTH].to_vec()
        };

        // The same digest and key give the same nonce, and the signature verifies.
        let unsigned = prove(VECTOR_MESSAGE);
        let first = unsigned.clone().sign(&ask, &fvk, ZeroRng).unwrap();
        let second = unsigned.sign(&ask, &fvk, ZeroRng).unwrap();
        assert_eq!(nonce_commitment(&first), nonce_commitment(&second));
        assert_eq!(
            first.verify(verifying_key(), &address, CoinType::MAINNET, VECTOR_MESSAGE),
            Ok(())
        );

        // A different digest gives a different nonce.
        let other = prove(b"another message").sign(&ask, &fvk, ZeroRng).unwrap();
        assert_ne!(nonce_commitment(&first), nonce_commitment(&other));
    }

    #[test]
    fn signatures_for_one_address_use_fresh_keys() {
        let (sk, address) = vector_address();
        let first = sign(&sk, &address, CoinType::MAINNET, VECTOR_MESSAGE).unwrap();
        let second = sign(&sk, &address, CoinType::MAINNET, VECTOR_MESSAGE).unwrap();
        assert_ne!(first.rk, second.rk);
        assert_ne!(first.proof, second.proof);
    }

    #[test]
    fn rejects_non_canonical_encodings() {
        let (sk, address) = vector_address();
        let encoded = encode(&sign(&sk, &address, CoinType::MAINNET, VECTOR_MESSAGE).unwrap());
        let rk = VERSION_LENGTH..VERSION_LENGTH + RK_LENGTH;
        assert_eq!(rk.end + SPEND_AUTH_SIG_LENGTH + PROOF_SIZE, SIGNATURE_SIZE);

        // An unknown version.
        let mut unknown_version = encoded;
        unknown_version[0] = VERSION + 1;
        assert!(AddressSignature::from_bytes(&unknown_version).is_none());

        // The identity as rk. Its encoding is all zeroes.
        let mut identity_rk = encoded;
        identity_rk[rk.clone()].fill(0);
        assert!(AddressSignature::from_bytes(&identity_rk).is_none());

        // An rk encoding that is not a field element.
        let mut non_canonical_rk = encoded;
        non_canonical_rk[rk].fill(u8::MAX);
        assert!(AddressSignature::from_bytes(&non_canonical_rk).is_none());
    }
}
