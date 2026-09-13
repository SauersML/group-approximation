# Part 4 (exec'd after the slab-edge check): local signs of the slab letters on the four edges adjacent to e' = {p, q}.
# sign_p / sign_q: sign of the permutation of the two outer edges at p / at q (for elements fixing p and q);
# sgn4: sign of the permutation of the four outer vertices {p1, p2, q1, q2} (defined for all of Stab(e')).
print("== outer-edge signs at e'")
q = nbrs[0]
NQ = [mm2(q, Nk) for Nk in NB]
outer = [nbrs[1], nbrs[2]] + [v for v in NQ if dist(v, p) != 0]
assert len(outer) == 4, len(outer)
def idx(Pm):
    for k, v in enumerate(outer):
        if dist(Pm, v) == 0:
            return k
    return None
def sign(perm):
    s, seen = 1, set()
    for i in range(len(perm)):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j); j = perm[j]; L += 1
        if L % 2 == 0:
            s = -s
    return s
for wd in ("a", "b", "c", "x", "z", "xz"):
    Mx = M3[wd]
    perm = [idx(mm2(Mx, v)) for v in outer]
    ok = None not in perm and sorted(perm) == [0, 1, 2, 3]
    s4 = sign(perm) if ok else None
    sp = sign([perm[0], perm[1]]) if ok and set(perm[:2]) == {0, 1} else None
    sq = sign([perm[2] - 2, perm[3] - 2]) if ok and set(perm[2:]) == {2, 3} else None
    print("word %-2s perm on (p1,p2,q1,q2) = %s  sgn4 = %s  sign_p = %s  sign_q = %s" % (wd, perm, s4, sp, sq))
print("DONE6")
