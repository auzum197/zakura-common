#!/usr/bin/env python3
"""Compares the constants of the Lean development with the constants of the Rust
code.

Usage (from `formal/address-signature-circuit`, after `lake update`):
    python3 scripts/check_constants.py

The Lean proof uses these constants of the Ironwood formalization, and one constant
of `AddressSignature/Spec.lean`:

* the Sinsemilla generator table `S` (1,024 points);
* the initial point `Q` of the `Commit^ivk` hash;
* for the fixed bases `SpendAuthG` and `CommitIvkR`: the generator, and the `z` and
  `u` values of the 85 windows.

The script reads the same constants from the Rust sources and fails if a value
differs. It does not compare the Lagrange coefficients: the Rust code computes them
at run time. They are the unique polynomials of degree 7 through the 8 points of each
window, and the Ironwood certificate proves this property for its coefficients.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(PROJECT))
IRONWOOD = os.path.join(PROJECT, ".lake", "packages", "Zcash", "Zcash", "Circuits")
RUST_CONSTANTS = os.path.join(REPO, "crates", "orchard", "src", "backend", "halo2", "constants")

failures = []


def check(name, ok):
    print("%-58s %s" % (name, "OK" if ok else "FAIL"))
    if not ok:
        failures.append(name)


def read(path):
    with open(path) as f:
        return f.read()


def ints(text):
    return [int(t.replace("_", ""), 0) for t in re.findall(r"0x[0-9a-fA-F_]+|\d[\d_]*", text)]


def le_bytes(values):
    assert len(values) == 32
    return sum(b << (8 * i) for i, b in enumerate(values))


def rust_const(text, name):
    """The body of `pub const NAME: … = …;` or `pub static NAME: … = …;`."""
    m = re.search(r"pub (?:const|static) %s\b[^=]*=(.*?);\n" % name, text, re.S)
    assert m, name
    return m.group(1)


def byte_arrays(body):
    """All `[u8; 32]` literals of a constant body, as integers."""
    values = ints(body)
    assert len(values) % 32 == 0
    return [le_bytes(values[i:i + 32]) for i in range(0, len(values), 32)]


def lean_def(text, name):
    """The body of `private def name … := […]` up to the next blank line."""
    m = re.search(r"def %s\b[^\n]*:=(.*?)\n\n" % name, text, re.S)
    assert m, name
    return m.group(1)


# The initial point Q of Commit^ivk.
rust_q = byte_arrays(rust_const(read(os.path.join(RUST_CONSTANTS, "sinsemilla.rs")),
                                "Q_COMMIT_IVK_M_GENERATOR"))
spec = read(os.path.join(PROJECT, "AddressSignature", "Spec.lean"))
lean_q = ints(re.search(r"def ivkQ : Point Fp :=(.*?)\n\n", spec, re.S).group(1))
check("Q of Commit^ivk (Spec.lean)", rust_q == lean_q)

# The Sinsemilla generator table.
rust_s_text = rust_const(read(os.path.join(REPO, "crates", "sinsemilla", "src", "sinsemilla_s.rs")),
                         "SINSEMILLA_S")
limbs = [int(t.replace("_", ""), 16) for t in re.findall(r"0x[0-9a-fA-F_]+", rust_s_text)]
assert len(limbs) == 1024 * 2 * 4
rust_s = [sum(l << (64 * i) for i, l in enumerate(limbs[j:j + 4])) for j in range(0, len(limbs), 4)]
lean_s = ints(lean_def(read(os.path.join(IRONWOOD, "Specs", "SinsemillaGenerators.lean")), "sData"))
check("Sinsemilla generator table, 1024 points (Ironwood)", rust_s == lean_s and len(lean_s) == 2048)

# The fixed bases.
for rust_name, lean_name in [("spend_auth_g", "SpendAuthG"), ("commit_ivk_r", "CommitIvkR")]:
    rust = read(os.path.join(RUST_CONSTANTS, "fixed_bases", rust_name + ".rs"))
    lean = read(os.path.join(IRONWOOD, "Ecc", "MulFixed", "Certs", lean_name + ".lean"))
    generator = byte_arrays(rust_const(rust, "GENERATOR"))
    base = ints(re.search(r"\{ base := \((.*?)\)", lean, re.S).group(1))
    check("%s generator (Ironwood)" % lean_name, generator == base)
    rust_z = ints(rust_const(rust, "Z").split("=")[-1])
    lean_z = ints(lean_def(lean, "zsData"))
    check("%s z values, 85 windows (Ironwood)" % lean_name, rust_z == lean_z and len(lean_z) == 85)
    rust_u = byte_arrays(rust_const(rust, "U"))
    lean_u = ints(lean_def(lean, "usData"))
    check("%s u values, 85 x 8 (Ironwood)" % lean_name, rust_u == lean_u and len(lean_u) == 680)

if failures:
    sys.exit("FAIL: %d constant(s) differ" % len(failures))
print("All constants match.")
