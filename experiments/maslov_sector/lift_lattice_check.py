import json, sys
pres = json.load(open(sys.argv[1]))
rels = pres["relators"]; lifts = pres["lifts"]
def egcd(a, b):
    if b == 0: return (a, 1, 0)
    g, x, y = egcd(b, a % b); return (g, y, x - (a // b) * y)
def hnf_insert(basis, v):
    """basis: list of rows in echelon form (pivot columns increasing). Insert v (list of ints)."""
    v = v[:]
    for row in basis:
        p = next(i for i, x in enumerate(row) if x != 0)
        if v[p] == 0: continue
        # combine row and v to zero out v[p] via extended gcd, updating basis row to gcd pivot
        g, x, y = egcd(row[p], v[p])
        r_new = [x*row[i] + y*v[i] for i in range(len(v))]
        v_new = [(v[p]//g)*row[i] - (row[p]//g)*v[i] for i in range(len(v))]
        row[:] = r_new; v = v_new
    if any(v):
        basis.append(v)
        basis.sort(key=lambda r: next(i for i, x in enumerate(r) if x != 0))
    return basis
def run(mod):
    basis = []
    for r, k in zip(rels, lifts):
        v = [0]*9
        for a in r:
            if a < 8: v[a] += 1
            else: v[a-8] -= 1
        v[8] = k
        basis = hnf_insert(basis, v)
    # rows with zero generator part
    central = [row[8] for row in basis if not any(row[:8])]
    c0 = 0
    for c in central:
        from math import gcd
        c0 = gcd(c0, abs(c))
    print("echelon basis rows:", len(basis))
    for row in basis: print("  ", row)
    print(f"central relation generator c0 = {c0} (zeta^c0 lies in the commutator subgroup of the presented group)")
    print(f"scalar solutions exist in mod-{mod} sector iff {mod} | c0 :", (c0 % mod == 0) if c0 else True)
run(3)
