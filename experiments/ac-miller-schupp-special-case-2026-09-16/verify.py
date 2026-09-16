#!/usr/bin/env python3
"""Independent replay of an AC chain printed by acsearch.

Each line is a pair of words.  A step P -> Q is accepted when there are
  * i != j, a rotation a of P[i], a rotation b of P[j], a sign e,
  * a signed permutation s of {x, y} (an automorphism of F_2),
such that Q equals s applied to (cycred(a * b^e), P[j]) up to cyclic
permutation, inversion of each relator and order of the two relators.
Every accepted step is a composite of (AC1)-(AC3) followed by an automorphism
of F_2 that permutes/inverts generators; AC-triviality is invariant under such
automorphisms, so a chain ending in a relator of length 1 shows the first
presentation is AC-trivial.
Usage: verify.py chainfile "rel1" "rel2"
"""
import sys
INV = {'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y'}

def free_red(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)

def cyc_red(w):
    w = free_red(w)
    while len(w) >= 2 and w[0] == INV[w[-1]]:
        w = w[1:-1]
    return w

def inverse(w):
    return ''.join(INV[c] for c in reversed(w))

def cyc_class(w):
    w = cyc_red(w)
    if not w:
        return ''
    rots = [w[k:] + w[:k] for k in range(len(w))]
    wi = inverse(w)
    rots += [wi[k:] + wi[:k] for k in range(len(wi))]
    return min(rots)

def pres_class(p):
    return tuple(sorted(cyc_class(r) for r in p))

SYMS = []
for swap in (0, 1):
    for sx in (0, 1):
        for sy in (0, 1):
            m = {}
            ix, iy = ('y', 'x') if swap else ('x', 'y')
            m['x'] = ix if not sx else INV[ix]
            m['X'] = INV[m['x']]
            m['y'] = iy if not sy else INV[iy]
            m['Y'] = INV[m['y']]
            SYMS.append(m)

def apply(s, w):
    return ''.join(s[c] for c in w)

def sym_classes(p):
    return {pres_class(tuple(apply(s, r) for r in p)) for s in SYMS}

def neighbours(p):
    res = set()
    for i in (0, 1):
        j = 1 - i
        ri, rj = p[i], p[j]
        for a in range(len(ri)):
            ra = ri[a:] + ri[:a]
            for b in range(len(rj)):
                rb = rj[b:] + rj[:b]
                for e in (rb, inverse(rb)):
                    res.add(pres_class((cyc_red(ra + e), rj)))
    return res

def main():
    lines = [l.split() for l in open(sys.argv[1]) if l.strip() and l.split()[0][0] in 'xXyY1']
    chain = [tuple('' if t == '1' else t for t in l[:2]) for l in lines]
    start = (sys.argv[2], sys.argv[3])
    assert pres_class(chain[0]) in sym_classes(start), 'first state is not the input up to symmetry'
    for k in range(len(chain) - 1):
        nb = neighbours(chain[k])
        tgt = sym_classes(chain[k + 1])
        assert nb & tgt, f'step {k} not an AC neighbour: {chain[k]} -> {chain[k+1]}'
    last = chain[-1]
    assert min(len(r) for r in last) == 1, 'chain does not end with a length-1 relator'
    # length-1 relator g^{+-1}: the other relator reduces mod g to a power of the other
    # generator whose exponent must be +-1 (the group is trivial); check it.
    g = [r for r in last if len(r) == 1][0]
    other = last[1] if last[0] == g else last[0]
    gen = g.lower()
    rest = ''.join(c for c in other if c.lower() != gen)
    other_gen = 'y' if gen == 'x' else 'x'
    exp = sum(1 if c == other_gen else -1 for c in rest)
    assert abs(exp) == 1, 'final presentation not trivial'
    print(f'VERIFIED chain of {len(chain)} states; AC-trivial')

if __name__ == '__main__':
    main()
