#!/usr/bin/env python3
"""Reads the pinned description of the address signature circuit and writes the
gate and lookup polynomials as Lean definitions.

Usage:
    python3 scripts/pinned.py DESCRIPTION OUTPUT.lean
    python3 scripts/pinned.py --check DESCRIPTION EXISTING.lean

The description is the `Debug` output of the pinned verifying key:
`crates/orchard/src/circuit_data/circuit_description_address_signature_v1`.

The script:

1. parses the 60 gate polynomials and the 3 lookup input expressions;
2. splits each gate polynomial into `selector expression * constraint`;
3. checks the structure against the Lean model (column counts, gate group sizes,
   selector columns, table columns, permutation columns);
4. writes `AddressSignature/Pinned.lean`. The file `AddressSignature/PinnedCheck.lean`
   proves that each generated polynomial is equal to the polynomial of the model.

With `--check`, the script compares its output with an existing file and fails if
they differ.
"""

import re
import sys

# The field of the circuit is the scalar field of Vesta, which is the base field of
# Pallas. The description names it `scalar_modulus`.
P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

# The number of constraints of each gate, in the order of `Assignment.gates`.
GATE_SIZES = [1, 12, 4, 2, 2, 6, 4, 2, 3, 5, 2, 2, 1, 7, 7]
GATE_NAMES = [
    "point", "add", "fixedWindow", "fixedAdd", "mul1", "mul2", "mul3", "mulComplete",
    "mulLsb", "mulOverflow", "sinInit", "sin", "shift", "commitIvkAk", "commitIvkNk",
]

# Fixed columns, in the order in which `Config::configure` creates them.
LAGRANGE = range(0, 8)
FIXED_Z_PLUS_ONE = 8
F_LOOKUP = 9
TABLE = [10, 11, 12]
SELECTOR_COLUMNS = [13, 14, 15]

TOKEN = re.compile(r'\s*(0x[0-9a-fA-F]+|-?\d+|[A-Za-z_][A-Za-z_0-9]*|"[^"]*"|[(){}\[\],:])')


def tokenize(text):
    pos, out = 0, []
    while True:
        m = TOKEN.match(text, pos)
        if not m:
            if text[pos:].strip():
                raise ValueError("cannot tokenize at %r" % text[pos:pos + 40])
            return out
        out.append(m.group(1))
        pos = m.end()


class Parser:
    def __init__(self, tokens):
        self.t, self.i = tokens, 0

    def peek(self):
        return self.t[self.i]

    def take(self, expected=None):
        tok = self.t[self.i]
        if expected is not None and tok != expected:
            raise ValueError("expected %r, found %r at token %d" % (expected, tok, self.i))
        self.i += 1
        return tok

    def value(self):
        tok = self.take()
        if tok == "[":
            items = []
            while self.peek() != "]":
                items.append(self.value())
                if self.peek() == ",":
                    self.take()
            self.take("]")
            return items
        if tok == "(":
            items = []
            while self.peek() != ")":
                items.append(self.value())
                if self.peek() == ",":
                    self.take()
            self.take(")")
            return ("", items)
        if tok.startswith("0x"):
            return int(tok, 16)
        if re.fullmatch(r"-?\d+", tok):
            return int(tok)
        if tok.startswith('"'):
            return tok[1:-1]
        # An identifier: a unit value, a tuple struct, or a struct.
        if self.i < len(self.t) and self.peek() == "(":
            self.take("(")
            items = []
            while self.peek() != ")":
                items.append(self.value())
                if self.peek() == ",":
                    self.take()
            self.take(")")
            return (tok, items)
        if self.i < len(self.t) and self.peek() == "{":
            self.take("{")
            fields = {}
            while self.peek() != "}":
                name = self.take()
                self.take(":")
                fields[name] = self.value()
                if self.peek() == ",":
                    self.take()
            self.take("}")
            return (tok, fields)
        return (tok, None)


def rotation(fields):
    name, items = fields["rotation"]
    assert name == "Rotation"
    return items[0]


def columns_of(e, kind):
    name, body = e
    if name == kind:
        return {body["column_index"]}
    if name in ("Constant",):
        return set()
    if name in ("Fixed", "Advice", "Instance"):
        return set()
    if name == "Negated":
        return columns_of(body[0], kind)
    if name in ("Sum", "Product"):
        return columns_of(body[0], kind) | columns_of(body[1], kind)
    if name == "Scaled":
        return columns_of(body[0], kind)
    raise ValueError("unknown expression %r" % name)


def count_fixed(e):
    name, body = e
    if name == "Fixed":
        return 1
    if name == "Constant":
        return 0
    if name in ("Negated", "Scaled"):
        return count_fixed(body[0])
    return count_fixed(body[0]) + count_fixed(body[1])


def row(k):
    assert k >= 0, "the model has no negative rotation"
    return "r" if k == 0 else "(r + %d)" % k


def lean(e, selector_var=None):
    """The Lean term of an expression. `selector_var` names the value of the fixed
    column in a selector expression."""
    name, body = e
    if name == "Constant":
        return "(%d : Fp)" % body[0]
    if name == "Advice":
        return "w.a%d %s" % (body["column_index"], row(rotation(body)))
    if name == "Fixed":
        c, k = body["column_index"], rotation(body)
        if selector_var is not None:
            assert k == 0
            return selector_var
        if c in LAGRANGE:
            return "w.lagrange %d %s" % (c, row(k))
        if c == FIXED_Z_PLUS_ONE:
            return "w.fixedZPlusOne %s" % row(k)
        if c == F_LOOKUP:
            return "w.fLookup %s" % row(k)
        raise ValueError("fixed column %d in a constraint" % c)
    if name == "Negated":
        return "(-%s)" % lean(body[0], selector_var)
    if name == "Sum":
        return "(%s + %s)" % (lean(body[0], selector_var), lean(body[1], selector_var))
    if name == "Product":
        return "(%s * %s)" % (lean(body[0], selector_var), lean(body[1], selector_var))
    if name == "Scaled":
        return "(%s * (%d : Fp))" % (lean(body[0], selector_var), body[1])
    raise ValueError("unknown expression %r" % name)


def evaluate_selector(e, value):
    name, body = e
    if name == "Constant":
        return body[0] % P
    if name == "Fixed":
        return value % P
    if name == "Negated":
        return (-evaluate_selector(body[0], value)) % P
    if name == "Sum":
        return (evaluate_selector(body[0], value) + evaluate_selector(body[1], value)) % P
    if name == "Product":
        return (evaluate_selector(body[0], value) * evaluate_selector(body[1], value)) % P
    if name == "Scaled":
        return (evaluate_selector(body[0], value) * body[1]) % P
    raise ValueError(name)


def generate(description):
    root = Parser(tokenize(description)).value()
    assert root[0] == "PinnedVerificationKey"
    vk = root[1]
    assert int(vk["scalar_modulus"], 16) == P
    cs = vk["cs"][1]
    assert cs["num_fixed_columns"] == 16
    assert cs["num_advice_columns"] == 3
    assert cs["num_instance_columns"] == 1
    assert cs["num_selectors"] == 13
    gates = cs["gates"]
    assert len(gates) == sum(GATE_SIZES) == 60

    # The permutation argument has the three advice columns and the instance column.
    perm = cs["permutation"][1]["columns"]
    perm_columns = sorted((c[1]["column_type"][0], c[1]["index"]) for c in perm)
    assert perm_columns == [("Advice", 0), ("Advice", 1), ("Advice", 2), ("Instance", 0)], perm_columns

    out = []
    out.append("import AddressSignature.Gates")
    out.append("")
    out.append("/-!")
    out.append("# The polynomials of the pinned circuit description")
    out.append("")
    out.append("This file is generated by `scripts/pinned.py` from")
    out.append("`crates/orchard/src/circuit_data/circuit_description_address_signature_v1`.")
    out.append("Do not edit it. `PinnedCheck.lean` proves that these polynomials are those of")
    out.append("the model in `Gates.lean`.")
    out.append("")
    out.append("Each gate polynomial of the description is `selector * constraint`. For each")
    out.append("gate, `<gate>Polys` is the list of its constraints, and `<gate>Selector f` is")
    out.append("its selector expression as a function of the value `f` of its fixed column.")
    out.append("-/")
    out.append("")
    out.append("namespace AddressSignature.Pinned")
    out.append("")
    out.append("open AddressSignature")
    out.append("")

    index = 0
    table = []
    for name, size in zip(GATE_NAMES, GATE_SIZES):
        selectors, constraints = [], []
        for e in gates[index:index + size]:
            assert e[0] == "Product", "a gate polynomial is selector * constraint"
            selector, constraint = e[1]
            assert not columns_of(selector, "Advice")
            assert not columns_of(constraint, "Fixed") & set(SELECTOR_COLUMNS + TABLE)
            selectors.append(selector)
            constraints.append(constraint)
        index += size
        assert all(s == selectors[0] for s in selectors), "one selector for each gate"
        selector = selectors[0]
        columns = columns_of(selector, "Fixed")
        assert len(columns) == 1
        column = columns.pop()
        if name == "fixedWindow":
            assert column == FIXED_Z_PLUS_ONE and selector[0] == "Fixed"
            active = None
        elif name == "sin":
            assert column == F_LOOKUP
            active = [v for v in range(0, 3) if evaluate_selector(selector, v) != 0]
            assert active == [1]
        else:
            assert column in SELECTOR_COLUMNS
            # A packed selector column holds 0, or the index of the enabled selector.
            # The index is at most the number of selectors in the column, which is
            # the degree of the selector expression.
            degree = count_fixed(selector)
            active = [v for v in range(0, degree + 1) if evaluate_selector(selector, v) != 0]
            assert len(active) == 1 and active[0] >= 1, (name, active)
        table.append((name, column, active))

        out.append("/-- The selector expression of gate `%s`: fixed column %d." % (name, column))
        if active is not None:
            out.append("It is not zero for the value %d, and zero for each other value that the" % active[0])
            out.append("column holds. -/")
        else:
            out.append("It is the column itself. -/")
        out.append("def %sSelector (f : Fp) : Fp :=" % name)
        out.append("  %s" % lean(selector, "f"))
        out.append("")
        out.append("/-- The constraints of gate `%s`. -/" % name)
        out.append("def %sPolys (w : Assignment) (r : ℕ) : List Fp :=" % name)
        body = ",\n    ".join(lean(c) for c in constraints)
        out.append("  [ %s ]" % body)
        out.append("")

    lookups = cs["lookups"]
    assert len(lookups) == 1
    inputs = lookups[0][1]["input_expressions"]
    tables = lookups[0][1]["table_expressions"]
    assert len(inputs) == 3
    assert [t[1]["column_index"] for t in tables] == TABLE
    assert all(t[0] == "Fixed" and rotation(t[1]) == 0 for t in tables)
    for name, e in zip(["lookupIndex", "lookupX", "lookupY"], inputs):
        assert not columns_of(e, "Fixed") & set(SELECTOR_COLUMNS + TABLE)
        out.append("/-- Input expression `%s` of the lookup. -/" % name)
        out.append("def %s (w : Assignment) (r : ℕ) : Fp :=" % name)
        out.append("  %s" % lean(e))
        out.append("")

    # The lookup defaults to the first table row `(0, x(S_0), y(S_0))`. The two
    # coordinates are the scaling constants of the last term of `x` and `y`.
    for name, e in zip(["initX", "initY"], inputs[1:]):
        assert e[0] == "Sum" and e[1][1][0] == "Scaled"
        out.append("/-- The constant `%s` of the lookup: a coordinate of the first table row. -/" % name)
        out.append("def %s : Fp := (%d : Fp)" % (name, e[1][1][1][1]))
        out.append("")

    out.append("/-- The fixed column and the enabling value of the selector of each gate. -/")
    out.append("def selectorTable : List (String × ℕ × Option ℕ) :=")
    rows = ",\n    ".join(
        '("%s", %d, %s)' % (n, c, "none" if a is None else "some %d" % a[0]) for n, c, a in table
    )
    out.append("  [ %s ]" % rows)
    out.append("")
    out.append("end AddressSignature.Pinned")
    out.append("")
    return "\n".join(out), table


def main(argv):
    check = argv[1:2] == ["--check"]
    args = argv[2:] if check else argv[1:]
    if len(args) != 2:
        sys.exit(__doc__)
    text, table = generate(open(args[0]).read())
    if check:
        if open(args[1]).read() != text:
            sys.exit("FAIL: %s is not the output of this script for %s" % (args[1], args[0]))
        print("OK: %s matches the pinned description" % args[1])
    else:
        open(args[1], "w").write(text)
        for name, column, active in table:
            print("%-12s fixed column %2d  enabled by %s" % (name, column, active))


if __name__ == "__main__":
    main(sys.argv)
