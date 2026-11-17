//! Off-chain signatures that bind a message to an Orchard address.
//!
//! There are two schemes. They prove different claims and they are deliberately
//! separate: they have separate types, encodings, and hash domains, and no function
//! accepts both. A verifier chooses the claim it requires before it parses a
//! signature.
//!
//! - [`spend_authority`] proves control of the spend authority of the address. Only a
//!   holder of the spend authorizing key can sign. A signature contains a Halo 2 proof.
//! - [`receive_authority`] proves knowledge of the incoming viewing key of the
//!   address. Each party that the viewing key was shared with can sign. It does not
//!   prove control of funds.
//!
//! A spend-authority signature implies receive authority. The reverse is never true.
//! A verifier that requires spend authority must not accept a receive-authority
//! signature as a fallback.
//!
//! Both schemes sign for the Orchard receiver only. For a Unified Address, a signature
//! says nothing about the other receivers. The Orchard protocol is used by the Orchard
//! and Ironwood pools, so one address is covered for both.
//!
//! These schemes are available on the Halo 2 backend only.

pub mod receive_authority;

#[cfg(any(feature = "prover", feature = "verifier"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "prover", feature = "verifier"))))]
pub mod spend_authority;

use alloc::{string::String, vec::Vec};

use base64::Engine;

/// The character that ends the prefix of a text encoding. It is not a Base64
/// character, so a text encoding has one prefix only.
const TEXT_PREFIX_END: char = ':';

/// The text encoding of a signature: the prefix, `:`, and the standard Base64
/// encoding, with padding, of the raw encoding.
fn encode_text(prefix: &str, raw: &[u8]) -> String {
    let mut text = String::from(prefix);
    text.push(TEXT_PREFIX_END);
    base64::engine::general_purpose::STANDARD.encode_string(raw, &mut text);
    text
}

/// Decodes a text encoding with the given prefix to the raw encoding.
///
/// Returns `None` if the text does not start with the prefix and `:`, or if the
/// remaining text is not canonical standard Base64 with padding.
fn decode_text(prefix: &str, text: &str) -> Option<Vec<u8>> {
    let encoded = text.strip_prefix(prefix)?.strip_prefix(TEXT_PREFIX_END)?;
    base64::engine::general_purpose::STANDARD
        .decode(encoded)
        .ok()
}

/// SLIP 44 coin type of Zcash Mainnet, in its index form.
const SLIP44_MAINNET: u32 = 133;

/// SLIP 44 coin type that all test networks share, in its index form.
const SLIP44_TESTNET: u32 = 1;

/// Length in bytes of the encoded coin type.
const COIN_TYPE_LENGTH: usize = 4;

/// Length in bytes of the ASCII prefix of a digest personalization.
const PERSONALIZATION_PREFIX_LENGTH: usize = 12;

/// Length in bytes of a BLAKE2b personalization.
const PERSONALIZATION_LENGTH: usize = PERSONALIZATION_PREFIX_LENGTH + COIN_TYPE_LENGTH;

/// Length in bytes of a message digest.
const DIGEST_LENGTH: usize = 32;

/// The network that an address signature is valid on.
///
/// The coin type is part of the hash personalization, so a signature for one network
/// does not verify on the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoinType(u32);

impl CoinType {
    /// Zcash Mainnet.
    pub const MAINNET: Self = CoinType(SLIP44_MAINNET);

    /// Zcash Testnet.
    pub const TESTNET: Self = CoinType(SLIP44_TESTNET);

    /// The 16-byte BLAKE2b personalization: `prefix` followed by the 4-byte
    /// little-endian coin type.
    fn personalization(
        self,
        prefix: &[u8; PERSONALIZATION_PREFIX_LENGTH],
    ) -> [u8; PERSONALIZATION_LENGTH] {
        let mut personalization = [0u8; PERSONALIZATION_LENGTH];
        personalization[..PERSONALIZATION_PREFIX_LENGTH].copy_from_slice(prefix);
        personalization[PERSONALIZATION_PREFIX_LENGTH..].copy_from_slice(&self.0.to_le_bytes());
        personalization
    }

    /// `BLAKE2b-256(prefix || coinType, parts[0] || parts[1] || ...)`.
    fn digest(
        self,
        prefix: &[u8; PERSONALIZATION_PREFIX_LENGTH],
        parts: &[&[u8]],
    ) -> [u8; DIGEST_LENGTH] {
        let mut state = blake2b_simd::Params::new()
            .hash_length(DIGEST_LENGTH)
            .personal(&self.personalization(prefix))
            .to_state();
        for part in parts {
            state.update(part);
        }
        let mut digest = [0u8; DIGEST_LENGTH];
        digest.copy_from_slice(state.finalize().as_bytes());
        digest
    }
}

/// The coin type is not the SLIP 44 coin type of Zcash Mainnet or of a test network.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnknownCoinType;

impl core::fmt::Display for UnknownCoinType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("unknown SLIP 44 coin type for Zcash")
    }
}

impl core::error::Error for UnknownCoinType {}

/// Converts a SLIP 44 coin type in its index form: 133 for Mainnet, and 1 for a test
/// network. This is the value that a wallet's network parameters give.
impl TryFrom<u32> for CoinType {
    type Error = UnknownCoinType;

    fn try_from(coin_type: u32) -> Result<Self, Self::Error> {
        match coin_type {
            SLIP44_MAINNET => Ok(Self::MAINNET),
            SLIP44_TESTNET => Ok(Self::TESTNET),
            _ => Err(UnknownCoinType),
        }
    }
}

/// A text is not the text encoding of a signature of the expected scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidTextEncoding;

impl core::fmt::Display for InvalidTextEncoding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("invalid text encoding of an address signature")
    }
}

impl core::error::Error for InvalidTextEncoding {}

#[cfg(test)]
mod tests {
    use super::{CoinType, SLIP44_MAINNET, SLIP44_TESTNET, UnknownCoinType};

    #[test]
    fn coin_type_from_slip44_index() {
        /// The hardened form of the Mainnet coin type, which is not the index form.
        const HARDENED_MAINNET: u32 = SLIP44_MAINNET | (1 << 31);

        assert_eq!(CoinType::try_from(SLIP44_MAINNET), Ok(CoinType::MAINNET));
        assert_eq!(CoinType::try_from(SLIP44_TESTNET), Ok(CoinType::TESTNET));
        for unknown in [0, SLIP44_TESTNET + 1, HARDENED_MAINNET] {
            assert_eq!(CoinType::try_from(unknown), Err(UnknownCoinType));
        }
    }
}

/// Generators for property testing.
#[cfg(any(test, feature = "test-dependencies"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
pub mod testing {
    use proptest::prelude::*;

    use super::CoinType;

    /// Generates a coin type.
    pub fn arb_coin_type() -> impl Strategy<Value = CoinType> {
        prop_oneof![Just(CoinType::MAINNET), Just(CoinType::TESTNET)]
    }
}
