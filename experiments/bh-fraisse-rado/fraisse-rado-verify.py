#!/usr/bin/env python3
# Independent verifier: works with explicit clopen sets (unions of dyadic cones) and a
# hand classification of pair orbits, never with the atom-colour abstraction.
# Completeness: the pattern of (U, z) depends only on which atoms of the family z meets
# and which it contains; one extra level of cones realizes every such colouring.
import itertools, json, sys

NAMES = ["complementary", "disjoint", "nested", "covering-overlap", "generic-overlap"]

def orbit(U, z, full):
    a, b, c, d = U & z != 0, U & ~z & full != 0, z & ~U & full != 0, full & ~(U | z) != 0
    if not a and not d:
        return 0  # z is the complement of U
    if not a:
        return 1  # disjoint, union not everything
    if not b or not c:
        return 2  # one contains the other
    if not d:
        return 3  # overlapping, union everything
    return 4      # overlapping, all four atoms nonempty

def family_from_atoms(atoms, depth):
    ncones = 2 ** depth
    r = len(atoms)
    assert r <= ncones
    owner = [min(j, r - 1) for j in range(ncones)]
    k = len(atoms[0])
    fam = []
    for i in range(k):
        U = 0
        for j in range(ncones):
            if atoms[owner[j]][i]:
                U |= 1 << j
        fam.append(U)
    return fam

def refine(U, depth):
    out = 0
    for j in range(2 ** depth):
        if (U >> j) & 1:
            out |= 0b11 << (2 * j)
    return out

def unrealized(mask, fam, v, depth):
    full = (1 << 2 ** depth) - 1
    assert all(0 < U < full for U in fam) and len(set(fam)) == len(fam)
    for z in range(1, full):
        if z in fam:
            continue
        vec = tuple((mask >> orbit(U, z, full)) & 1 for U in fam)
        if vec == tuple(v):
            return False, z
    return True, None

certs = [json.loads(l) for l in open(sys.argv[1]) if l.strip().startswith("{")]
ok = 0
for c in certs:
    fam3 = family_from_atoms(c["atoms"], 3)
    fam4 = [refine(U, 3) for U in fam3]
    good, z = unrealized(c["mask"], fam4, c["v"], 4)
    names = [NAMES[i] for i in range(5) if (c["mask"] >> i) & 1]
    print("mask", c["mask"], names, "K", c["K"], "family(depth3 cones)", [format(U, "08b") for U in fam3], "v", c["v"], "VERIFIED" if good else "REALIZED by z=%s" % format(z, "016b"))
    ok += good
print("CERTS", len(certs), "VERIFIED", ok)

# positive control: masks with no K<=2 certificate must pass the 2-point extension
# property on every family of two distinct depth-2 clopens (<= 4 atoms, complete).
surv = [c["mask"] for c in certs if c["K"] == 3]
full2 = 15
sets2 = list(range(1, full2))
ctrl_ok = True
for mask in surv:
    for U1, U2 in itertools.combinations(sets2, 2):
        f = [refine(U1, 2), refine(U2, 2)]
        for v in itertools.product((0, 1), repeat=2):
            good, _ = unrealized(mask, f, v, 3)
            if good:
                ctrl_ok = False
                print("CONTROL FAIL mask", mask, U1, U2, v)
print("POSITIVE CONTROL (K=2 survivors pass 2-point extension):", "PASS" if ctrl_ok else "FAIL", "survivors", surv)

# negative control: a corrupted certificate (all-adjacent vector for the mask of all
# five orbits minus one, on a two-set family) must be reported as realized.
bad = {"mask": 0b01111, "atoms": [[1, 0], [0, 1], [1, 1], [0, 0]], "v": [1, 1]}
fam3 = family_from_atoms(bad["atoms"], 3)
good, z = unrealized(bad["mask"], [refine(U, 3) for U in fam3], bad["v"], 4)
print("NEGATIVE CONTROL (corrupted certificate rejected):", "PASS" if not good else "FAIL")
