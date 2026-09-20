"""Exact strong irreducibility test for nearest-neighbour SFTs on F_2 = <a, b> (bitmask version of
verify_bank.py part (3)).

treesft.is_si / si_defect only test PATH mixing (a necessary condition). SI is equivalent to
HALF-TREE mixing HM(r): for every vertex v entered by letter delta and every globally admissible
pattern on a finite set F of the half-tree below v with d(v, F) >= r, every symbol of E extends.
  SI(R)  => HM(R): take the second pattern to be a single symbol at v.
  HM(r)  => SI(2r - 1): see verify_bank.py docstring.

hm(Ra, Rb, n, E) returns the least r with HM(r), or None if the family of W-sets never becomes {E}.
"""
from treesft import essential, restrict, transpose

INV = [1, 0, 3, 2]


def _preds(M, n, E):
    """pred(W) = {s in E : M[s] & W}; returned as a function on bitmasks, cached."""
    cache = {}

    def f(W):
        r = cache.get(W)
        if r is None:
            r = 0
            for s in range(n):
                if E >> s & 1 and M[s] & W:
                    r |= 1 << s
            cache[W] = r
        return r
    return f


def _combine(delta, fam, fixes, P):
    acc = {-1}
    for eps in range(4):
        if eps == INV[delta]:
            continue
        Ps = {P[eps](W) for W in fam[eps]}
        acc = {X & Y for X in acc for Y in Ps if X & Y}
    return {X & f for X in acc for f in fixes if X & f}


def hm(Ra, Rb, n, E=None, maxk=200, maxfam=20000, witness=None):
    """witness: optional list; on failure it receives the recurring W-set families (per entry letter)."""
    if E is None:
        E = essential(Ra, Rb, n)
    if E == 0:
        return None
    Ra, Rb = restrict(Ra, E, n), restrict(Rb, E, n)
    Ms = [Ra, transpose(Ra, n), Rb, transpose(Rb, n)]
    P = [_preds(M, n, E) for M in Ms]
    singles = [1 << s for s in range(n) if E >> s & 1]
    fixes0 = [E] + singles
    fam = [{E} | set(singles) for _ in range(4)]
    while True:
        new = [fam[dl] | {X & E for X in _combine(dl, fam, fixes0, P)} for dl in range(4)]
        if new == fam:
            break
        fam = new
        if max(len(f) for f in fam) > maxfam:
            raise RuntimeError("W-set family too large")
    seen = set()
    for k in range(1, maxk):
        fam = [{X & E for X in _combine(dl, fam, [E], P)} | {E} for dl in range(4)]
        if all(f == {E} for f in fam):
            return k
        key = tuple(frozenset(f) for f in fam)
        if key in seen:
            if witness is not None:
                witness.extend(fam)
            return None
        seen.add(key)
    return None
