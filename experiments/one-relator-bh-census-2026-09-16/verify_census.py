#!/usr/bin/env python3
"""Independent re-check of the JSON lines written by census.py.

Written separately from census.py and sharing no code with it.  Letters are encoded as
integers (a = 1, t = 2, inverses negative).  For every record it checks:

  sigma   the endomorphism sigma of F(a,t) given by the record is an automorphism: the
          Stallings folding of the two petals sigma(a), sigma(t), trimmed of hanging trees,
          is the one-vertex rose (then <sigma(a), sigma(t)> = F_2, and F_2 is Hopfian);
  img     img is a cyclic rotation of the cyclic reduction of sigma(w), hence conjugate to
          sigma(w), so <a,t | w> = <a,t | img>;
  tag     the tag's condition, recomputed from img (or from w for POWER):
            PRIM      |img| = 1;
            POWER     w = root^k with k >= 2;
            TORUS     img is a cyclic rotation of a^p t^q with |p|, |q| >= 2;
            FBC       t-exponent sum 0 and the lowest and highest a-levels each carry one letter;
            BS        img is a rotation of a^f t^n a^e t^-n (any signs) with n = 1;
            POWERMAP  the same shape with n >= 2 and min(|e|, |f|) = 1;
            C16       6 * (longest piece of the symmetrized closure of img) < |img|;
            VFBC      the CERT line is for img and the committed verify.py accepts it;
  classes the representatives of each length L are distinct, each is the least word of its
          orbit under rotation, inversion and the eight signed letter permutations, and the
          orbit sizes add up to the number 3^L + (-1)^L + 2 of cyclically reduced words of
          length L (brute-force recount for L <= 8).  So the census covers every relator.
Usage: verify_census.py FILE.jsonl
"""
import sys, os, json, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'research', 'artifacts', 'or-length15-residue-scripts'))
import verify as vf   # committed independent checker of vfib.py CERT lines

ENC = {'a': 1, 'A': -1, 't': 2, 'T': -2}
DEC = {v: k for k, v in ENC.items()}

def enc(s):
    return [ENC[c] for c in s]

def dec(u):
    return ''.join(DEC[x] for x in u)

def reduce_free(u):
    out = []
    for x in u:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out

def reduce_cyc(u):
    u = reduce_free(u)
    while len(u) >= 2 and u[0] == -u[-1]:
        u = u[1:-1]
    return u

def invert(u):
    return [-x for x in reversed(u)]

def apply(sig, u):
    im = {1: enc(sig['a']), 2: enc(sig['t'])}
    out = []
    for x in u:
        out.extend(im[x] if x > 0 else invert(im[-x]))
    return reduce_free(out)

def is_automorphism(sig):
    """Stallings folding of the petals sigma(a), sigma(t) based at vertex 0."""
    edges, nv = set(), 1
    for word in (enc(sig['a']), enc(sig['t'])):
        word = reduce_free(word)
        if not word:
            return False
        cur = 0
        for i, x in enumerate(word):
            if i == len(word) - 1:
                nxt = 0
            else:
                nxt, nv = nv, nv + 1
            edges.add((cur, x, nxt) if x > 0 else (nxt, -x, cur))
            cur = nxt
    while True:   # fold: two edges with the same label leaving (or entering) one vertex
        merge = None
        seen = {}
        for u, l, v in sorted(edges):
            for key, other in ((('o', u, l), v), (('i', v, l), u)):
                if key in seen and seen[key] != other:
                    merge = (seen[key], other); break
                seen[key] = other
            if merge:
                break
        if merge is None:
            break
        x, y = sorted(merge)          # keep the smaller label, so vertex 0 survives
        edges = {(x if p == y else p, l, x if q == y else q) for p, l, q in edges}
    while True:   # trim hanging trees away from the base vertex
        deg = {}
        for u, l, v in edges:
            deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
        leaves = {x for x, d in deg.items() if d == 1 and x != 0}
        if not leaves:
            break
        edges = {(u, l, v) for u, l, v in edges if u not in leaves and v not in leaves}
    return edges == {(0, 1, 0), (0, 2, 0)}

def rotations(u):
    return [u[i:] + u[:i] for i in range(len(u))]

def shape_two_syllable(u):
    """If u is a rotation of a^f t^n a^e t^-n (signs arbitrary), return (n, e, f)."""
    for r in rotations(u):
        b = []
        for x in r:
            if b and b[-1][0] == x:
                b[-1][1] += 1
            else:
                b.append([x, 1])
        if len(b) == 4 and abs(b[0][0]) == 1 and abs(b[2][0]) == 1 and abs(b[1][0]) == 2 \
                and b[3][0] == -b[1][0] and b[1][1] == b[3][1]:
            sgn = lambda y: 1 if y > 0 else -1
            return b[1][1], sgn(b[2][0]) * b[2][1], sgn(b[0][0]) * b[0][1]
    return None

def torus_shape(u):
    for r in rotations(u):
        b = []
        for x in r:
            if b and b[-1][0] == x:
                b[-1][1] += 1
            else:
                b.append([x, 1])
        if len(b) == 2 and abs(b[0][0]) != abs(b[1][0]) and min(b[0][1], b[1][1]) >= 2:
            return True
    return False

def fbc_condition(u):
    if sum(1 if x == 2 else -1 for x in u if abs(x) == 2) != 0:
        return False
    h, lv = 0, []
    for x in u:
        if abs(x) == 2:
            h += 1 if x > 0 else -1
        else:
            lv.append(h)
    if not lv:
        return False
    lo, hi = min(lv), max(lv)
    return hi > lo and lv.count(lo) == 1 and lv.count(hi) == 1

def longest_piece(u):
    L = len(u)
    R = {tuple(r) for v in (u, invert(u)) for r in rotations(v)}
    best = 0
    for p, q in itertools.combinations(R, 2):
        k = 0
        while k < L and p[k] == q[k]:
            k += 1
        best = max(best, k)
    return best

PERMS = []
for swap in (0, 1):
    for sa in (1, -1):
        for st in (1, -1):
            PERMS.append({1: (2 if swap else 1) * sa, 2: (1 if swap else 2) * st})

def orbit(s):
    u = enc(s)
    orb = set()
    for P in PERMS:
        v = [P[x] if x > 0 else -P[-x] for x in u]
        for z in (v, invert(v)):
            for r in rotations(z):
                orb.add(dec(r))
    return orb

def count_cyclically_reduced(L):
    return 3 ** L + (-1) ** L + 2

def brute_count(L):
    return sum(1 for u in itertools.product((1, -1, 2, -2), repeat=L)
               if all(u[i] != -u[(i + 1) % L] for i in range(L)))

def check(rec):
    w, tag = rec['w'], rec['tag']
    u = enc(w)
    if reduce_cyc(u) != u:
        return 'FAIL w not cyclically reduced'
    if tag == 'RESIDUE':
        return 'residue'
    if tag == 'POWER':
        k, root = rec['k'], rec['root']
        return 'ok' if k >= 2 and root * k == w else 'FAIL power'
    sig, img = rec['sigma'], rec['img']
    if not is_automorphism(sig):
        return 'FAIL sigma not an automorphism'
    c = reduce_cyc(apply(sig, u))
    if enc(img) not in rotations(c):
        return 'FAIL img is not a rotation of cred(sigma(w))'
    v = enc(img)
    if tag == 'PRIM':
        return 'ok' if len(v) == 1 else 'FAIL prim'
    if tag == 'TORUS':
        return 'ok' if torus_shape(v) else 'FAIL torus'
    if tag == 'FBC':
        return 'ok' if fbc_condition(v) else 'FAIL fbc'
    if tag in ('BS', 'POWERMAP'):
        sh = shape_two_syllable(v)
        if sh is None:
            return 'FAIL two-syllable shape'
        n, e, f = sh
        if tag == 'BS':
            return 'ok' if n == 1 else 'FAIL bs'
        return 'ok' if n >= 2 and min(abs(e), abs(f)) == 1 else 'FAIL powermap'
    if tag == 'C16':
        return 'ok' if 6 * longest_piece(v) < len(v) else 'FAIL c16'
    if tag == 'VFBC':
        line = rec['vfib']
        if line.split()[1] != img:
            return 'FAIL vfib word != img'
        res = vf.verify(line)
        return 'ok' if res.startswith('VERIFIED') else 'FAIL vfib ' + res
    return 'FAIL unknown tag'

def main():
    recs = [json.loads(line) for line in open(sys.argv[1])]
    byL, bad, tally = {}, 0, {}
    for r in recs:
        res = check(r)
        tally[(r['L'], r['tag'])] = tally.get((r['L'], r['tag']), 0) + 1
        if res.startswith('FAIL'):
            bad += 1; print(res, r['w'], r['tag'])
        byL.setdefault(r['L'], []).append(r['w'])
    for L in sorted(byL):
        reps = byL[L]
        total, seen = 0, set()
        for s in reps:
            if len(s) != L:
                bad += 1; print('FAIL length', s)
            orb = orbit(s)
            if min(orb) != s or s in seen:
                bad += 1; print('FAIL representative', s)
            seen.add(s); total += len(orb)
        expect = count_cyclically_reduced(L)
        if L <= 8 and brute_count(L) != expect:
            bad += 1; print('FAIL count formula', L)
        ok = total == expect
        bad += 0 if ok else 1
        tags = sorted((t, c) for (l, t), c in tally.items() if l == L)
        print('L=%d classes=%d words=%d expected=%d complete=%s %s' % (L, len(reps), total, expect, ok, tags))
    print('TOTAL FAILURES', bad)
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
