#!/usr/bin/env python3
"""Checks the layout model of the Lean proof against the keygen layout of the circuit.

The Lean hypothesis `Wired` (AddressSignature/Layout.lean) says which selector rows,
fixed cells, and copy constraints the circuit has. This script states the same facts
and checks each of them against `fixtures/addressSignatureLayout.json`, which the Rust
test `dump_address_signature_fixtures` records from the real `configure` and
`synthesize`. It also checks the reverse: the circuit enables no selector, assigns no
fixed cell, and creates no copy constraint that the model does not name.

The facts in this script are a transcription of `Wired`. The script does not read
`Layout.lean`. A change of `Wired` needs the same change here.

Run from the project directory: `python3 scripts/check_layout.py`.
To record the fixture again, see the documentation of the Rust test.
"""
import re, sys, json, os
from collections import defaultdict

P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IW = D + "/.lake/packages/Zcash/Zcash/Circuits"

layout = json.load(open(D + "/fixtures/addressSignatureLayout.json"))
K = layout["k"]
assert layout["constants"] == [], "the circuit has no constants column"

# Fixed cells. The fixture has the packed selector columns 13, 14, 15, and it has the
# generator-table fill expanded up to the last usable row.
TABLE = (10, 11, 12)
PACKED = {13: ["q_point", "q_add", "q_fixed_add", "q_mul_1"],
          14: ["q_mul_2", "q_mul_3", "q_mul_complete", "q_mul_lsb", "q_mul_overflow"],
          15: ["q_sin_init", "q_shift", "q_commit_ivk_ak", "q_commit_ivk_nk"]}
SELNAMES = ["q_point","q_add","q_fixed_add","q_mul_1","q_mul_2","q_mul_3","q_mul_complete",
            "q_mul_lsb","q_mul_overflow","q_sin_init","q_shift","q_commit_ivk_ak","q_commit_ivk_nk"]
S = {n: i for i, n in enumerate(SELNAMES)}

sel = defaultdict(set)   # selector index -> rows
fixed = {}               # (column, row) -> value, without table and packed columns
table = {}
for c, r, v in layout["fixed"]:
    if c in PACKED:
        # A packed column holds the 1-based index of its enabled selector
        # (`SelectorsPacked` in PinnedSoundness.lean).
        assert 1 <= v <= len(PACKED[c]), ("packed selector value", c, r, v)
        sel[S[PACKED[c][v - 1]]].add(r)
    elif c in TABLE:
        assert (c, r) not in table; table[(c, r)] = v
    else:
        assert c < 10 and (c, r) not in fixed, ("fixed cell", c, r)
        fixed[(c, r)] = v
usable = max(r for (c, r) in table) + 1
print("usable rows n =", usable)

perm = [(kind[0].upper(), index) for kind, index in layout["permColumns"]]
assert perm == [("A", 0), ("A", 1), ("A", 2), ("I", 0)], perm
copies = [((perm[a], ra), (perm[b], rb)) for a, ra, b, rb in layout["copyList"]]
regions = [dict(name=name, start=start) for _, name, start in layout["regions"]]
LAG, ZP1, FL = list(range(8)), 8, 9

results = []
def chk(name, ok, detail=""):
    results.append((name, ok))
    print("%-4s %s %s" % ("PASS" if ok else "FAIL", name, detail if not ok else ""))

# ---------- Placement ----------
PL = [("gd","witness point",1),("ak","witness point",1),
 ("alphaMul","fixed-base mul (incomplete addition)",170),("alphaAdd","complete addition",4),
 ("rkAdd","complete addition",4),("b0","short range check",2),("b2","short range check",2),
 ("d0","short range check",2),("hash","Sinsemilla hash",104),
 ("rivkMul","fixed-base mul (incomplete addition)",170),("rivkAdd","complete addition",4),
 ("commitAdd","complete addition",4),("aPrime","range check",14),("b2cPrime","range check",15),
 ("canonAk","CommitIvk canonicity of ak",3),("canonNk","CommitIvk canonicity of nk",3),
 ("dbl","complete addition",4),("inc","variable-base mul (incomplete addition)",506),
 ("bit0","variable-base mul (complete bit)",2),("addU0","complete addition",4),("addAcc0","complete addition",4),
 ("bit1","variable-base mul (complete bit)",2),("addU1","complete addition",4),("addAcc1","complete addition",4),
 ("bit2","variable-base mul (complete bit)",2),("addU2","complete addition",4),("addAcc2","complete addition",4),
 ("lsb","variable-base mul (least significant bit)",2),("lsbAdd","complete addition",4),
 ("sRange","range check",14),("overflow","variable-base mul (overflow check)",3),("pkd","check point",1)]
assert regions[0]["name"] == "generator table"
regs = regions[1:]
chk("Placement: 32 regions", len(regs) == 32, str(len(regs)))
L = {}; size = {}
okn = True
for (f, nme, sz), rg in zip(PL, regs):
    if rg["name"] != nme: okn = False; print("  name mismatch", f, nme, rg["name"])
    L[f] = rg["start"]; size[f] = sz
chk("Placement: region names/order = Placement order", okn)
print("L =", json.dumps(L))
iv = sorted((L[f], L[f] + size[f], f) for f in L)
chk("regions do not overlap (model sizes)", all(iv[i][1] <= iv[i+1][0] for i in range(len(iv)-1)))
for f in L:
    chk("fits %-9s : L+%d <= n" % (f, size[f]), L[f] + size[f] <= usable)

# ---------- union find ----------
par = {}
def find(x):
    par.setdefault(x, x)
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x
def union(a, b): par[find(a)] = find(b)
for a, b in copies: union(a, b)
A0 = lambda r: (("A", 0), r)
A1 = lambda r: (("A", 1), r)
A2 = lambda r: (("A", 2), r)
INST = lambda r: (("I", 0), r)
model_eqs = []
def eq(name, a, b):
    model_eqs.append((a, b))
    chk("copy  " + name, find(a) == find(b), "%s vs %s" % (a, b))
def eqpt01(name, r1, r2): eq(name + ".x", A0(r1), A0(r2)); eq(name + ".y", A1(r1), A1(r2))
model_sel = set()
def selon(name, s, r):
    model_sel.add((S[s], r)); chk("sel   %s: %s row %d" % (name, s, r), r in sel[S[s]])
model_fix = set()
def fx(name, c, r, v):
    model_fix.add((c, r)); got = fixed.get((c, r), 0)
    chk("fixed %s: col %d row %d" % (name, c, r), got == v % P, "got %x want %x" % (got, v % P))

# ---------- Ironwood constants ----------
def ints(text): return [int(t) for t in re.findall(r"\d+", text)]
def lean_def(text, name):
    return re.search(r"def %s\b[^\n]*:=(.*?)\n\n" % name, text, re.S).group(1)
def base_params(fname):
    t = open(IW + "/Ecc/MulFixed/Certs/" + fname + ".lean").read()
    zs = ints(lean_def(t, "zsData")); cf = ints(lean_def(t, "coeffsData"))
    assert len(zs) == 85 and len(cf) == 680
    return zs, [cf[8*i:8*i+8] for i in range(85)]
spec = open(D + "/AddressSignature/Spec.lean").read()
QX, QY = ints(re.search(r"def ivkQ : Point Fp :=(.*?)\n\n", spec, re.S).group(1).replace("Fp", ""))[:2]

# ---------- nested structures ----------
def fixedMul(name, fname, o):
    zs, cf = base_params(fname)
    bad = []
    for j in range(85):
        r = o + 2*j
        model_fix.add((ZP1, r))
        if fixed.get((ZP1, r), 0) != (zs[j] + 1) % P: bad.append(("z", j))
        for i in range(8):
            model_fix.add((i, r))
            if fixed.get((i, r), 0) != cf[j][i] % P: bad.append(("lag", j, i))
    chk("fixed %s.params: z+1 and 8 Lagrange coeffs = Ironwood %s.params j, 85 windows" % (name, fname), not bad, str(bad[:5]))
    bad = [j for j in range(1, 84) if (o + 2*j) not in sel[S["q_fixed_add"]]]
    for j in range(1, 84): model_sel.add((S["q_fixed_add"], o + 2*j))
    chk("sel   %s.fixedAdd: q_fixed_add rows o+2j, j=1..83" % name, not bad, str(bad[:5]))
    eq(name + ".copyX", A1(o + 3), A1(o)); eq(name + ".copyY", A2(o + 3), A2(o))

def shortRC(name, o, bits):
    selon(name + ".shift", "q_shift", o)
    fx(name + ".factor (lagrange[0] = 2^(10-%d))" % bits, 0, o, 2 ** (10 - bits))
    fx(name + ".lookup0", FL, o, 2); fx(name + ".mode0", 2, o, 0)
    fx(name + ".lookup1", FL, o + 1, 2); fx(name + ".mode1", 2, o + 1, 0)

def rangeRC(name, o, num):
    b1 = [i for i in range(num) if fixed.get((FL, o + i), 0) != 2]
    b2 = [i for i in range(num) if fixed.get((2, o + i), 0) != 1]
    for i in range(num): model_fix.add((FL, o + i)); model_fix.add((2, o + i))
    chk("fixed %s.lookup: f_lookup = 2 rows o..o+%d" % (name, num - 1), not b1, str(b1))
    chk("fixed %s.mode: f_s2 = 1 rows o..o+%d" % (name, num - 1), not b2, str(b2))

def sinMode(j): return 0 if j in (24, 25, 49) else (2 if j == 50 else 1)
def sinsemilla(name, o):
    selon(name + ".init", "q_sin_init", o)
    fx(name + ".xQ = ivkQ.x (Spec.lean)", 0, o, QX); fx(name + ".yQ = ivkQ.y (Spec.lean)", 1, o, QY)
    b1 = [j for j in range(51) if fixed.get((FL, o + 2*j), 0) != 1]
    b2 = [j for j in range(51) if fixed.get((2, o + 2*j), 0) != sinMode(j)]
    for j in range(51): model_fix.add((FL, o + 2*j)); model_fix.add((2, o + 2*j))
    chk("fixed %s.lookup: f_lookup = 1 rows o+2j, j<51" % name, not b1, str(b1))
    chk("fixed %s.mode: f_s2 = sinMode j rows o+2j, j<51" % name, not b2, str(b2))

def completeBit(name, ob, ou, oa):
    selon(name + ".sel", "q_mul_complete", ob); selon(name + ".addU", "q_add", ou); selon(name + ".addAcc", "q_add", oa)
    eq(name + ".uy", A1(ou), A2(ob)); eqpt01(name + ".acc", oa, ou + 1); eqpt01(name + ".tmp", oa + 1, ou + 2)

# ---------- Wired ----------
selon("gdSel", "q_point", L["gd"]); eq("gdX", A0(L["gd"]), INST(0)); eq("gdY", A1(L["gd"]), INST(1))
selon("akSel", "q_point", L["ak"])
fixedMul("alphaMul", "SpendAuthG", L["alphaMul"])
selon("alphaAddSel", "q_add", L["alphaAdd"])
eq("alphaAddP.x", A0(L["alphaAdd"]), A1(L["alphaMul"] + 168)); eq("alphaAddP.y", A1(L["alphaAdd"]), A2(L["alphaMul"] + 168))
eq("alphaAddQ.x", A0(L["alphaAdd"] + 1), A1(L["alphaMul"] + 169)); eq("alphaAddQ.y", A1(L["alphaAdd"] + 1), A2(L["alphaMul"] + 169))
selon("rkSel", "q_add", L["rkAdd"])
eqpt01("rkP", L["rkAdd"], L["alphaAdd"] + 2); eqpt01("rkQ", L["rkAdd"] + 1, L["ak"])
eq("rkX", A0(L["rkAdd"] + 2), INST(4)); eq("rkY", A1(L["rkAdd"] + 2), INST(5))
shortRC("b0", L["b0"], 4); shortRC("b2", L["b2"], 5); shortRC("d0", L["d0"], 9)
sinsemilla("hash", L["hash"])
fixedMul("rivkMul", "CommitIvkR", L["rivkMul"])
selon("rivkAddSel", "q_add", L["rivkAdd"])
eq("rivkAddP.x", A0(L["rivkAdd"]), A1(L["rivkMul"] + 168)); eq("rivkAddP.y", A1(L["rivkAdd"]), A2(L["rivkMul"] + 168))
eq("rivkAddQ.x", A0(L["rivkAdd"] + 1), A1(L["rivkMul"] + 169)); eq("rivkAddQ.y", A1(L["rivkAdd"] + 1), A2(L["rivkMul"] + 169))
selon("commitSel", "q_add", L["commitAdd"])
eqpt01("commitP", L["commitAdd"], L["hash"] + 102); eqpt01("commitQ", L["commitAdd"] + 1, L["rivkAdd"] + 2)
rangeRC("aPrime", L["aPrime"], 13); rangeRC("b2cPrime", L["b2cPrime"], 14)
oh, ob0_, ob2_, od0_, oap, obp, oka, okn_ = (L[k] for k in ["hash", "b0", "b2", "d0", "aPrime", "b2cPrime", "canonAk", "canonNk"])
selon("canon.selAk", "q_commit_ivk_ak", oka); selon("canon.selNk", "q_commit_ivk_nk", okn_)
eq("canon.a", A1(oka), A0(oh + 1)); eq("canon.b", A2(oka), A0(oh + 51))
eq("canon.b0", A0(oka + 1), A0(ob0_)); eq("canon.b2", A2(oka + 1), A0(ob2_))
eq("canon.z13a", A0(oka + 2), A0(oh + 27)); eq("canon.aPrime", A1(oka + 2), A0(oap))
eq("canon.z13aPrime", A2(oka + 2), A0(oap + 13))
eq("canon.c", A1(okn_), A0(oh + 53)); eq("canon.d", A2(okn_), A0(oh + 101))
eq("canon.d0", A0(okn_ + 1), A0(od0_)); eq("canon.b2'", A2(okn_ + 1), A0(ob2_))
eq("canon.z13c", A0(okn_ + 2), A0(oh + 79)); eq("canon.b2cPrime", A1(okn_ + 2), A0(obp))
eq("canon.z14b2cPrime", A2(okn_ + 2), A0(obp + 14))
eq("canonAkCopy", A0(oka), A0(L["ak"]))
# MulRegions
od, oi, ol, ola, os_, oo = (L[k] for k in ["dbl", "inc", "lsb", "lsbAdd", "sRange", "overflow"])
selon("mul.dbl", "q_add", od)
selon("mul.inc.mul1", "q_mul_1", oi)
bad = [r for r in range(250) if (oi + 2*(r+1)) not in sel[S["q_mul_2"]]]
for r in range(250): model_sel.add((S["q_mul_2"], oi + 2*(r+1)))
chk("sel   mul.inc.mul2: q_mul_2 rows oi+2(r+1), r<250", not bad, str(bad[:5]))
selon("mul.inc.mul3", "q_mul_3", oi + 502)
eq("mul.accY", A1(oi), A1(od + 2)); eq("mul.accX", A0(oi + 2), A0(od + 2))
B = [(L["bit%d" % i], L["addU%d" % i], L["addAcc%d" % i]) for i in range(3)]
for i, (ob, ou, oa) in enumerate(B): completeBit("mul.bit%d" % i, ob, ou, oa)
eq("mul.z0", A0(B[0][0]), A0(oi + 505)); eqpt01("mul.acc0", B[0][1] + 1, oi + 504)
eq("mul.z1", A0(B[1][0]), A0(B[0][0] + 1)); eqpt01("mul.acc1", B[1][1] + 1, B[0][2] + 2)
eq("mul.z2", A0(B[2][0]), A0(B[1][0] + 1)); eqpt01("mul.acc2", B[2][1] + 1, B[1][2] + 2)
selon("mul.lsb.sel", "q_mul_lsb", ol); selon("mul.lsb.add", "q_add", ola)
eq("mul.lsb.p.x", A0(ola), A1(ol)); eq("mul.lsb.p.y", A1(ola), A2(ol))
eq("mul.zl", A0(ol), A0(B[2][0] + 1)); eqpt01("mul.accl", ola + 1, B[2][2] + 2)
rangeRC("mul.sRange", os_, 13)
selon("mul.overflow", "q_mul_overflow", oo)
eq("mul.ovZ0", A0(oo), A0(ol + 1)); eq("mul.ovK254", A1(oo), A0(oi + 5)); eq("mul.ovS", A2(oo), A0(os_))
eq("mul.ovZ130", A0(oo + 1), A0(oi + 253)); eq("mul.ovSHi", A2(oo + 1), A0(os_ + 13))
# MulBase with P = pt01 L.gd
g = L["gd"]
eq("mulBase.dblP.x", A0(od), A0(g)); eq("mulBase.dblP.y", A1(od), A1(g))
eq("mulBase.dblQ.x", A0(od + 1), A0(g)); eq("mulBase.dblQ.y", A1(od + 1), A1(g))
eq("mulBase.incX", A1(oi + 3), A0(g)); eq("mulBase.incY", A2(oi + 3), A1(g))
for i, (ob, ou, oa) in enumerate(B):
    eq("mulBase.u%d" % i, A0(ou), A0(g)); eq("mulBase.b%d" % i, A1(ob), A1(g))
eq("mulBase.lsbX", A1(ol + 1), A0(g)); eq("mulBase.lsbY", A2(ol + 1), A1(g))
eq("mulScalar", A1(oo + 1), A0(L["commitAdd"] + 2))
selon("pkdSel", "q_point", L["pkd"]); eqpt01("pkdCopy", L["pkd"], ola + 2)
eq("pkdX", A0(L["pkd"]), INST(2)); eq("pkdY", A1(L["pkd"]), INST(3))

# MulFits sizes are in PL (dbl 4, inc 506, bits 2, adds 4, lsb 2, lsbAdd 4, sRange 14, overflow 3): checked by "fits".

# ---------- reverse direction ----------
print("\n== reverse direction ==")
real_sel = {(i, r) for i in sel for r in sel[i]}
extra = sorted(real_sel - model_sel)
chk("reverse: every enabled selector row is named by the model (%d real, %d model)" % (len(real_sel), len(model_sel)),
    not extra, str([(SELNAMES[i], r) for i, r in extra][:20]))
miss = sorted(model_sel - real_sel)
chk("model selector rows all enabled", not miss, str(miss[:10]))
real_fix_nz = {(c, r) for (c, r), v in fixed.items() if c < 10 and v != 0}
extra = sorted(real_fix_nz - model_fix)
chk("reverse: every nonzero fixed cell (cols 0..9) is named by the model (%d nonzero)" % len(real_fix_nz), not extra, str(extra[:20]))
real_fix_all = {(c, r) for (c, r) in fixed if c < 10}
print("     fixed cells assigned (cols 0..9): %d; assigned but not in model (value zero): %s" %
      (len(real_fix_all), sorted(real_fix_all - model_fix)[:20]))
zrows = {r for (c, r), v in fixed.items() if c == ZP1 and v != 0}
want = {L[b] + 2*j for b in ("alphaMul", "rivkMul") for j in range(85)}
chk("reverse: fixed_z_plus_one nonzero exactly on the 170 window rows", zrows == want, str(sorted(zrows ^ want)[:10]))
frows = {r: v for (c, r), v in fixed.items() if c == FL and v != 0}
wantf = {L["hash"] + 2*j: 1 for j in range(51)}
for b, n_ in (("aPrime", 13), ("b2cPrime", 14), ("sRange", 13)):
    for i in range(n_): wantf[L[b] + i] = 2
for b in ("b0", "b2", "d0"):
    wantf[L[b]] = 2; wantf[L[b] + 1] = 2
chk("reverse: f_lookup nonzero exactly on the model rows, with the model values", frows == wantf)
chk("f_lookup values are in {0,1,2}", set(frows.values()) <= {1, 2})
# model equalities union-find
mp = {}
def mfind(x):
    mp.setdefault(x, x)
    while mp[x] != x:
        mp[x] = mp[mp[x]]; x = mp[x]
    return x
for a, b in model_eqs: mp[mfind(a)] = mfind(b)
extra = [(a, b) for a, b in copies if mfind(a) != mfind(b)]
chk("reverse: every real copy constraint (%d) is implied by the model equalities" % len(copies), not extra, str(extra[:20]))
for e in extra: print("     real copy not in model:", e)
# hazard: readers of data cells in lagrange columns
print("\n== gates that read fixed data cells, per row ==")
haz = []
rowpurpose = {}
for f in L:
    for r in range(L[f], L[f] + size[f]): rowpurpose[r] = f
for r in range(1 << K):
    readers = []
    if fixed.get((ZP1, r), 0) != 0: readers.append("window")
    if r in sel[S["q_sin_init"]]: readers.append("sin_init")
    if r in sel[S["q_shift"]]: readers.append("shift")
    if fixed.get((FL, r), 0) != 0: readers.append("lookup/sin(f_s2)")
    f = rowpurpose.get(r)
    kind = None if f is None else dict(PL_KIND := {p[0]: p[1] for p in PL})[f]
    allowed = {"fixed-base mul (incomplete addition)": {"window"},
               "Sinsemilla hash": {"sin_init", "lookup/sin(f_s2)"},
               "short range check": {"shift", "lookup/sin(f_s2)"},
               "range check": {"lookup/sin(f_s2)"}}.get(kind, set())
    if set(readers) - allowed: haz.append((r, f, readers))
    if "window" in readers and len(readers) > 1: haz.append((r, f, readers))
chk("no row where a gate reads a lagrange/data cell written for another purpose", not haz, str(haz[:10]))

# ---------- table ----------
print("\n== table ==")
st = open(IW + "/Specs/SinsemillaGenerators.lean").read()
sd = ints(lean_def(st, "sData"))
assert len(sd) == 2048
bad = [i for i in range(1024) if (table.get((10, i)), table.get((11, i)), table.get((12, i))) != (i, sd[2*i], sd[2*i+1])]
chk("table: columns 10,11,12 rows 0..1023 = (i, x(S_i), y(S_i)) of Ironwood sData", not bad, str(bad[:5]))
bad = [r for r in range(1024, usable)
       if (table.get((10, r)), table.get((11, r)), table.get((12, r))) != (0, sd[0], sd[1])]
chk("table: rows 1024 to the last usable row = (0, x(S_0), y(S_0))", not bad, str(bad[:5]))
chk("table: no cell after the last usable row", all(r < usable for (_, r) in table))

nf = [n for n, ok in results if not ok]
print("\nTOTAL %d checks, %d FAIL" % (len(results), len(nf)))
for n in nf: print("  FAIL:", n)
sys.exit(1 if nf else 0)
