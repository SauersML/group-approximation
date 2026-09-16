#!/usr/bin/env python3
"""Stage C5: certify residue pairs after Nielsen transformations of F(x1, x2, x3).

A Nielsen move replaces x_i by x_i x_j^e or by x_j^e x_i (i != j, e = +-1) in both relators,
followed by free and cyclic reduction.  It is an automorphism of the free group, so the new
presentation defines an isomorphic group with the same H_1 = Z.  At every state reached we
apply:
  C1  a generator occurs exactly once in a relator (Tietze elimination leaves a two-generator
      one-relator homology circle; Barreto--Minian Thm 2.9 with k = 0);
  C2, C3, C6 as in census.py.
Breadth-first search, depth <= D, relator lengths <= LMAX.  Output: one certificate per residue
pair (the move sequence and the final test) or 'UNCERTIFIED'.

Usage: residue.py residue_file D LMAX out_file
"""
import sys, json
from math import gcd
from census import expvec, cross, certify, canon_ri


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def cyc_reduce(w):
    w = free_reduce(w)
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1
        j -= 1
    return tuple(w[i:j + 1])


def moves():
    out = []
    for i in (1, 2, 3):
        for j in (1, 2, 3):
            if i == j:
                continue
            for e in (1, -1):
                out.append(('R', i, j * e))   # x_i -> x_i x_j^e
                out.append(('L', i, j * e))   # x_i -> x_j^e x_i
    return out


MOVES = moves()


def apply_move(w, mv):
    side, i, y = mv
    out = []
    for x in w:
        if abs(x) != i:
            out.append(x)
        elif x > 0:
            out.extend((x, y) if side == 'R' else (y, x))
        else:
            out.extend((-y, x) if side == 'R' else (x, -y))
    return cyc_reduce(out)


def substitutions(ri, rj):
    """Relator substitution (an Andrews--Curtis move, hence the same group and H_1): if a cyclic
    rotation of rj^{+-1} splits as p q with |p| >= |q| and p is a cyclic subword of ri, replace
    that occurrence of p by q^{-1} and cyclically reduce.  Yields (new ri, description)."""
    n = len(ri)
    if n == 0:
        return
    seen = set()
    for e, w in ((1, rj), (-1, tuple(-x for x in reversed(rj)))):
        L = len(w)
        for rot in range(L):
            rho = w[rot:] + w[:rot]
            for lp in range((L + 1) // 2, L + 1):
                p, q = rho[:lp], rho[lp:]
                if lp > n:
                    break
                qinv = tuple(-x for x in reversed(q))
                doubled = ri + ri
                for start in range(n):
                    if doubled[start:start + lp] == p:
                        rest = doubled[start + lp:start + n]
                        new = cyc_reduce(list(qinv) + list(rest))
                        if new not in seen:
                            seen.add(new)
                            yield new, ['S', e, rot, lp, start]


def c1(r1, r2):
    for idx, r in ((1, r1), (2, r2)):
        for g in (1, 2, 3):
            if sum(1 for x in r if abs(x) == g) == 1:
                return ('C1', idx, g)
    return None


def test_state(r1, r2):
    if not r1 or not r2:
        return None
    c = cross(expvec(r1), expvec(r2))
    assert gcd(gcd(c[0], c[1]), c[2]) == 1
    t = c1(r1, r2)
    if t is not None:
        return t
    return certify(r1, r2, c)


def key(r1, r2):
    a, b = canon_ri(r1), canon_ri(r2)
    return (a, b) if a <= b else (b, a)


def search(r1, r2, D, LMAX):
    seen = {key(r1, r2)}
    frontier = [((r1, r2), [])]
    for depth in range(D + 1):
        nxt = []
        for (a, b), path in frontier:
            t = test_state(a, b)
            if t is not None:
                return {'moves': path, 'final': [list(a), list(b)], 'test': list(t)}
            if depth == D:
                continue
            cand = []
            for new, d in substitutions(b, a):
                cand.append(((a, new), ['S2'] + d[1:]))
            for new, d in substitutions(a, b):
                cand.append(((new, b), ['S1'] + d[1:]))
            for mv in MOVES:
                cand.append(((apply_move(a, mv), apply_move(b, mv)), list(mv)))
            for (a2, b2), d in cand:
                if len(a2) > LMAX or len(b2) > LMAX or not a2 or not b2:
                    continue
                k = key(a2, b2)
                if k in seen:
                    continue
                seen.add(k)
                nxt.append(((a2, b2), path + [d]))
        frontier = nxt
    return None


def main():
    fn, D, LMAX, outfn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    done = unc = 0
    with open(fn) as f, open(outfn, 'w') as g:
        for line in f:
            parts = line.split('|')
            r1 = tuple(int(x) for x in parts[0].split())
            r2 = tuple(int(x) for x in parts[1].split())
            cert = search(r1, r2, D, LMAX)
            if cert is None:
                unc += 1
                g.write(json.dumps({'r1': list(r1), 'r2': list(r2), 'cert': 'UNCERTIFIED'}) + '\n')
            else:
                done += 1
                g.write(json.dumps({'r1': list(r1), 'r2': list(r2), 'cert': cert}) + '\n')
    print('certified', done, 'uncertified', unc)


if __name__ == '__main__':
    main()
