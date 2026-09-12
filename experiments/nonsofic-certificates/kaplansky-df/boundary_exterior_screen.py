#!/usr/bin/env python3
"""Exact exterior-power kernel screen for half-corner chart comparisons.

Lane kaplansky-df. For a candidate Z in P_0 S f_0 (S = F_2[R^x]) this finds
vectors v in f_0 Lambda^k B with Z v = 0, where B is the boundary module of
R = L_{F_2}(1,2) on points w.T (T a fixed generic tail). A nonzero kernel vector
is an exact certificate that no L in S satisfies L Z = f_0: L Z v = 0 while
f_0 v = v != 0. Finding no kernel on a finite window proves nothing.

Uses the shared checker (leavitt, groupalg); run on MSI only.
Usage: python3 boundary_exterior_screen.py CHECKER_DIR OUT.json [--degree 2|3] [--window m]
"""
import itertools
import json
import random
import sys
import time

CHECKER = sys.argv[1]
OUT = sys.argv[2]
DEGREE = 2
WINDOW = 2
args = sys.argv[3:]
for i, a in enumerate(args):
    if a == "--degree":
        DEGREE = int(args[i + 1])
    if a == "--window":
        WINDOW = int(args[i + 1])
sys.path.insert(0, CHECKER)
import leavitt as L  # noqa: E402
import groupalg as GA  # noqa: E402

L.set_dual(False)
rng = random.Random(20260911)
TAIL = "".join(rng.choice("01") for _ in range(160))
LOG = {"started": time.strftime("%Y-%m-%d %H:%M:%S"), "degree": DEGREE, "window": WINDOW}


def order3(expr):
    val = L.parse_elem(expr)
    return L.Unit(val, val * val)


def thompson(domain, rng_words):
    return L.thompson_unit(domain.split(), rng_words.split())


def closure(gens):
    elems = {L.IDENTITY.key: L.IDENTITY}
    frontier = [L.IDENTITY]
    while frontier:
        new = []
        for x in frontier:
            for s in gens:
                y = x * s
                if y.key not in elems:
                    y = L.Unit(y.val, y.inv, check=False)
                    elems[y.key] = y
                    new.append(y)
        frontier = new
    return elems


def ga(units):
    return GA.GroupAlgebraElement(units)


ONE = ga([L.IDENTITY])

# --- the half-corner chart and its projectors -------------------------------
g = order3("(1 + S[00]T[01])(1 + S[01]T[00])")
u = thompson("0 10 11", "00 01 1")
child = u * g * u.inverse()
child = L.Unit(child.val, child.inv, check=False)
K = closure([g, child])
LOG["K_order"] = len(K)
E_parent = ga([g, g * g])
E_child = ga([child, child * child])
fplus = E_child + (E_child * E_parent * E_child) ** 2
P = E_parent + (E_parent * E_child * E_parent) ** 4
Kl = list(K.values())
center = [x for x in Kl if (x * g).key == (g * x).key and (x * child).key == (child * x).key]
z = [x for x in center if x.order() == 3][0]
comm = set()
comm_units = {}
for x in Kl:
    for y in Kl:
        c = x * y * x.inverse() * y.inverse()
        if c.key not in comm_units:
            comm_units[c.key] = L.Unit(c.val, c.inv, check=False)
A = closure(list(comm_units.values()))
LOG["A_order"] = len(A)
E = ga([L.IDENTITY, z, z * z]) * ga([a for a in A.values() if a.order() in (3, 5)])
f0 = fplus * (ONE + E)
P0 = P * (ONE + E)
LOG["supports"] = {"fplus": len(fplus), "P": len(P), "E": len(E), "f0": len(f0), "P0": len(P0)}
LOG["idempotent"] = {"f0": (f0 * f0 + f0).is_zero(), "P0": (P0 * P0 + P0).is_zero()}

# torus representatives on the leaves (000,001 | 010,011)
g00 = order3("(1 + S[000]T[001])(1 + S[001]T[000])")
g01 = order3("(1 + S[010]T[011])(1 + S[011]T[010])")
T0 = g00 * g01 * g01
T1 = g01 * g01
LOG["torus_in_K"] = {"T0": T0.key in K, "T1": T1.key in K}

# --- boundary action ---------------------------------------------------------
_tables = {}


def act(unit, point):
    t = _tables.get(unit.key)
    if t is None:
        t = unit.val.table()
        _tables[unit.key] = t
    out = t.evaluate(point)
    if out is None:
        raise RuntimeError("point too short for table")
    return out


def apply_units(units, vec):
    """vec: set of sorted tuples of DEGREE distinct points (an F_2 combination of wedges)."""
    res = set()
    for wedge in vec:
        for q in units:
            images = [act(q, p) for p in wedge]
            for combo in itertools.product(*images):
                if len(set(combo)) < len(combo):
                    continue
                key = tuple(sorted(combo))
                if key in res:
                    res.remove(key)
                else:
                    res.add(key)
    return res


def apply_ga(x, vec):
    return apply_units(x.support(), vec)


class Eliminator(object):
    def __init__(self):
        self.index = {}
        self.pivots = {}

    def encode(self, vec):
        n = 0
        for key in vec:
            i = self.index.get(key)
            if i is None:
                i = len(self.index)
                self.index[key] = i
            n |= 1 << i
        return n

    def reduce(self, n, comb):
        while n:
            top = n.bit_length() - 1
            piv = self.pivots.get(top)
            if piv is None:
                return n, comb
            n ^= piv[0]
            comb ^= piv[1]
        return 0, comb

    def add(self, n, comb):
        n, comb = self.reduce(n, comb)
        if n:
            self.pivots[n.bit_length() - 1] = (n, comb)
            return None
        return comb


def sector_basis(proj, degree, m):
    leaves = ["000", "001", "010", "011"]
    points = [leaf + "".join(w) + TAIL for leaf in leaves for w in itertools.product("01", repeat=m)]
    elim = Eliminator()
    basis = []
    for wedge in itertools.combinations(sorted(points), degree):
        v = apply_ga(proj, {wedge})
        if not v:
            continue
        if elim.add(elim.encode(v), 0) is None:
            basis.append(v)
    return basis


def kernel_of(stages, basis):
    elim = Eliminator()
    for i, b in enumerate(basis):
        v = b
        for st in stages:
            v = st(v)
        comb = elim.add(elim.encode(v), 1 << i)
        if comb is not None:
            return [i for i in range(len(basis)) if (comb >> i) & 1]
    return None


def stage_units(units):
    return lambda v: apply_units(units, v)


def stage_ga(x):
    return lambda v: apply_ga(x, v)


t0 = time.time()
basis = sector_basis(f0, DEGREE, WINDOW)
LOG["f0_sector_rank_on_window"] = len(basis)
LOG["P0_sector_rank_on_window"] = len(sector_basis(P0, DEGREE, WINDOW))
LOG["f0_kills_B"] = len(sector_basis(f0, 1, WINDOW)) == 0

# --- fusion transporters ------------------------------------------------------
sigma = thompson("00 010 011 1", "00 011 010 1")
lam = thompson("000 001 010 011 1", "000 010 001 011 1")
mu = thompson("0 10 11", "01 00 1")
phi = sigma * mu * lam * sigma
phi = L.Unit(phi.val, phi.inv, check=False)
conj = phi * T0 * phi.inverse()
LOG["phi_T0_phiinv"] = {"in_K": conj.key in K, "equals_T1": conj.key == T1.key,
                        "order": conj.order()}

candidates = {
    "control_P0f0": [stage_ga(P0)],
    "phi": [stage_units([phi]), stage_ga(P0)],
    "phi_inv": [stage_units([phi.inverse()]), stage_ga(P0)],
    "mu": [stage_units([mu]), stage_ga(P0)],
    "lam_mu": [stage_units([mu * lam]), stage_ga(P0)],
}
# coefficient-dressed fusion transporters P0 c [phi] d f0 with random chart coefficients
for trial in range(4):
    c = ga(rng.sample(Kl, 5))
    d = ga(rng.sample(Kl, 5))
    candidates["phi_dressed_%d" % trial] = [stage_ga(d), stage_units([phi]), stage_ga(c), stage_ga(P0)]
# two-transporter sums
candidates["phi_plus_phiinv"] = [stage_units([phi, phi.inverse()]), stage_ga(P0)]
candidates["phi_plus_mu"] = [stage_units([phi, mu]), stage_ga(P0)]

def xor_vecs(vecs):
    out = set()
    for v in vecs:
        out ^= v
    return out


def verify_kernel(stages, basis_used, ker):
    """Independent recomputation of a kernel certificate in dual mode."""
    L.set_dual(True)
    try:
        v = xor_vecs(basis_used[i] for i in ker)
        ok_nonzero = bool(v)
        ok_f0 = apply_ga(f0, v) == v
        w = v
        for st in stages:
            w = st(w)
        return {"nonzero": ok_nonzero, "f0_fixes": ok_f0, "Z_kills": not w}
    finally:
        L.set_dual(False)


results = {}
for name, stages in candidates.items():
    t1 = time.time()
    ker = kernel_of(stages, basis)
    results[name] = {"kernel_found": ker is not None,
                     "kernel_size": None if ker is None else len(ker),
                     "seconds": round(time.time() - t1, 2)}
    if ker is not None and name in ("phi", "phi_dressed_0", "phi_plus_mu"):
        results[name]["verified"] = verify_kernel(stages, basis, ker)
LOG["results"] = results


def complete_codes(max_size):
    codes = {("",)}
    frontier = [("",)]
    while frontier:
        new = []
        for code in frontier:
            if len(code) >= max_size:
                continue
            for i, leaf in enumerate(code):
                child_code = tuple(sorted(code[:i] + (leaf + "0", leaf + "1") + code[i + 1:]))
                if child_code not in codes:
                    codes.add(child_code)
                    new.append(child_code)
        frontier = new
    return sorted(codes, key=lambda c: (len(c), c))


# --- family: every single Thompson transporter with codes of size <= FAMILY_MAX ---
FAMILY_MAX = 4
for i, a in enumerate(args):
    if a == "--family-max":
        FAMILY_MAX = int(args[i + 1])
if "--rescreen" in args:
    FAMILY_MAX = 1  # skip the family pass; only rescreen a prior survivor list
codes = [c for c in complete_codes(FAMILY_MAX) if len(c) >= 2]
seen = set()
survivors = []
count = 0
t2 = time.time()
for dom in codes:
    for rng_code in codes:
        if len(dom) != len(rng_code):
            continue
        for perm in itertools.permutations(rng_code):
            try:
                tr = L.thompson_unit(list(dom), list(perm))
            except ValueError:
                continue
            if tr.key in seen or tr.is_identity():
                continue
            seen.add(tr.key)
            count += 1
            stages = [stage_units([tr]), stage_ga(P0)]
            if kernel_of(stages, basis) is None:
                survivors.append({"domain": list(dom), "range": list(perm)})
LOG["family"] = {"max_code_size": FAMILY_MAX, "transporters": count,
                 "degree2_window_survivors": len(survivors), "seconds": round(time.time() - t2, 2)}

# re-screen survivors in degree 3 on the same window
if survivors and DEGREE == 2:
    basis3 = sector_basis(f0, 3, WINDOW)
    LOG["f0_sector_rank_degree3_window"] = len(basis3)
    still = []
    for s in survivors:
        tr = L.thompson_unit(s["domain"], s["range"])
        if kernel_of([stage_units([tr]), stage_ga(P0)], basis3) is None:
            still.append(s)
    LOG["family"]["degree3_window_survivors"] = len(still)
    LOG["family"]["degree3_survivor_list"] = still[:200]

def is_uniform_on_chart(domain, range_words):
    """True when g^-1 carries the four chart leaves to cones of one common length.

    Then <K, g^-1 K g> lies in a finite uniform-depth group, and the torus fusion
    obstruction (chart-comparison-must-fuse-torus-classes) already kills
    P_0[g]f_0, whatever the exterior screen says on a window.
    """
    tr = L.thompson_unit(domain, range_words)
    inv = tr.inverse()
    lengths = set()
    for leaf in ("000", "001", "010", "011"):
        out = act(inv, leaf + TAIL)
        (x,) = tuple(out)
        lengths.add(len(x) - len(TAIL))
    return len(lengths) == 1


RESCREEN = None
for i, a in enumerate(args):
    if a == "--rescreen":
        RESCREEN = args[i + 1]
if RESCREEN:
    with open(RESCREEN) as fh:
        prior = json.load(fh)["family"]["degree3_survivor_list"]
    nonuniform = [s for s in prior if not is_uniform_on_chart(s["domain"], s["range"])]
    report = {"prior": len(prior), "nonuniform": len(nonuniform)}
    for deg in (2, 3):
        bas = sector_basis(f0, deg, WINDOW)
        report["f0_rank_degree%d" % deg] = len(bas)
        keep = []
        for s in nonuniform:
            tr = L.thompson_unit(s["domain"], s["range"])
            if kernel_of([stage_units([tr]), stage_ga(P0)], bas) is None:
                keep.append(s)
        nonuniform = keep
        report["survivors_after_degree%d" % deg] = len(keep)
    report["survivor_list"] = nonuniform
    LOG["rescreen"] = report

LOG["seconds_total"] = round(time.time() - t0, 2)
with open(OUT, "w") as fh:
    json.dump(LOG, fh, indent=1, sort_keys=True)
print(json.dumps(LOG, indent=1, sort_keys=True))
