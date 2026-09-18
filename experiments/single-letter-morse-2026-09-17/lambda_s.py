#!/usr/bin/env python3
"""Transport subgroup Lambda_s of a single-letter Morse scheme, with a Freiheitssatz witness of nonamenability.

For a cyclically reduced word w (list of (letter, exponent)) and a letter s, the cell (y, w) of the Bernoulli
Cayley 2-complex crosses s-edges based at h_i . y for each s-occurrence i, where (convention of
bernoulli-morse-collapse-criterion.md, Section 1, prefix p_i of length i):
    h_i = p_i^{-1}      if the occurrence is s^{+1},
    h_i = p_{i-1}^{-1}  if the occurrence is s^{-1}.
Lambda_s = < h_j h_i^{-1} >.  Its conjugate by h_i contains g_{ij} = h_i^{-1} h_j.

Witness (sufficient for nonamenability of Lambda_s in Gamma = <S | w>, w cyclically reduced):
two elements of Lambda_s (conjugated), given as reduced words in F(S), that avoid one letter occurring in w
and do not commute in the free group.  By the Freiheitssatz they then generate a free group of rank 2 in Gamma.

Run:  python3 lambda_s.py      (prints a table; exit 0)
"""
from itertools import product


def inv(u):
    return [(a, -e) for (a, e) in reversed(u)]


def red(u):
    out = []
    for x in u:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out


def mul(*us):
    r = []
    for u in us:
        r = red(r + list(u))
    return r


def parse(s):
    """'a b A' with capitals for inverses."""
    w = []
    for ch in s.replace(' ', ''):
        w.append((ch.lower(), 1 if ch.islower() else -1))
    return w


def show(u):
    return ''.join(a if e == 1 else a.upper() for a, e in u) or '1'


def bases(w, s):
    hs = []
    for i, (a, e) in enumerate(w, start=1):
        if a != s:
            continue
        p = w[:i] if e == 1 else w[:i - 1]
        hs.append(inv(red(p)))
    return hs


def commute(u, v):
    return mul(u, v) == mul(v, u)


def witness(w, s, depth=2):
    letters = sorted({a for a, _ in w})
    hs = bases(w, s)
    k = len(hs)
    if k < 2:
        return k, None
    best = None
    # Q generates Lambda_s; we also test conjugates c^{-1} Q c by prefixes of w and their inverses
    # (a conjugate of Lambda_s is nonamenable iff Lambda_s is).
    Q = [mul(hs[j], inv(hs[i])) for i in range(k) for j in range(k) if i != j]
    prefixes = [red(w[:i]) for i in range(len(w) + 1)]
    for c in prefixes + [inv(p) for p in prefixes]:
        gens = [mul(inv(c), q, c) for q in Q]
        pool = [g for g in gens]
        if depth >= 2:
            pool += [mul(g1, g2) for g1, g2 in product(gens, repeat=2)]
        pool = [g for g in pool if g]
        for u, v in product(pool, repeat=2):
            used = {a for a, _ in u} | {a for a, _ in v}
            missing = [c for c in letters if c not in used]
            if missing and not commute(u, v):
                cand = (len(u) + len(v), show(u), show(v), missing[0])
                if best is None or cand < best:
                    best = cand
    return k, best


EXAMPLES = [
    ("sbscsdbdcdbc", "every letter used 3 times; torsion-free"),
    ("abacad", "free group F(a,c,d); calibration (letter a thrice, b once)"),
    ("abAB", "Z^2; every letter twice (Lambda cyclic)"),
    ("taTAA", "BS(1,2); amenable, letter a thrice"),
    ("abaBabcdcDcd", "every letter used 3 times; torsion-free; all four Lambda_s nonamenable"),
]


def main():
    for word, note in EXAMPLES:
        w = parse(word)
        print(f"w = {word}   ({note})")
        for s in sorted({a for a, _ in w}):
            k, wit = witness(w, s)
            if k < 2:
                print(f"  s={s}: k={k}  (at most one occurrence: no children, no obstruction)")
            elif wit is None:
                print(f"  s={s}: k={k}  no Freiheitssatz witness found at depth 2")
            else:
                _, u, v, miss = wit
                print(f"  s={s}: k={k}  Lambda_s nonamenable: <{u}, {v}> is free of rank 2 (avoids {miss})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
