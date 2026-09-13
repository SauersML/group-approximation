#!/usr/bin/env python3
"""Cross-check of Claims A'1 and A'2 for one-sided loop weights on the three-equal residue shapes.

Lane kl-remaining-shapes, 2026-09-12.  Class +++++- of
`kl-length-six-coincidence-saturated-torsion-residue`:
    w = t a1 t a2 t a3 t a4 t y t^-1 x,
corners c0..c3 = P-edges t^- -> t^+ (labels a1..a4), c4 = Y loop at t^-, c5 = X loop at t^+.
A step along c_i forward reads a_i, backward a_i^-1; a path reads corners in counterclockwise
order around a region.

X-scheme (needs a1 = 1): theta 1 on the three heavy corners and on Y, 0 on the light corner and X.
  Transfers from pure X regions land on (Y of D', c0 of D): a Y step adjacent to a c0 step.
Y-scheme (needs a4 = 1): theta 1 on the heavy corners and on X, 0 on the light corner and Y.
  Transfers from pure Y regions land on (c3 of D, X of D'): an X step adjacent to a c3 step.

Labels live in U = F(g) * C_kx(x) * C_ky(y).  For each shape and scheme report:
  A. cycles with trivial label and W < 2 that are not pure powers of the zero-weight loop;
  B. cycles with trivial label, W < 3, and a transfer-loop step adjacent to the receiving corner;
  C. canonical nontrivial labels with W < 2 (relations a positive interior region needs);
  D. canonical nontrivial labels of cycles in B's class (relations a weak receiver needs).
"""
import sys

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 10
SRC = ['-', '-', '-', '-', '-', '+']
DST = ['+', '+', '+', '+', '-', '+']
LOOPNAME = {4: 'Y', 5: 'X'}
ORDERS = {}

def letter(ch):
    return () if ch == '1' else ((ch, 1),)

def inverse(word):
    return tuple((n, -e) for n, e in reversed(word))

def norm(n, e):
    o = ORDERS.get(n)
    if o:
        e %= o
        if e > o // 2:
            e -= o
    return e

def reduce_word(word):
    stack = []
    for n, e in word:
        if stack and stack[-1][0] == n:
            e += stack.pop()[1]
        e = norm(n, e)
        if e:
            stack.append((n, e))
    return tuple(stack)

def canonical_cyclic(word):
    w = list(reduce_word(word))
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        name, e = w[0][0], norm(w[0][0], w[0][1] + w[-1][1])
        w = w[1:-1]
        if e:
            w = [(name, e)] + w
        w = list(reduce_word(w))
    if not w:
        return ()
    cands = []
    for seq in (w, list(reduce_word(inverse(tuple(w))))):
        for k in range(len(seq)):
            cands.append(tuple(seq[k:] + seq[:k]))
    return min(cands)

def fmt(word):
    return ' '.join(n if e == 1 else '%s^%d' % (n, e) for n, e in word) or '1'

def run(shape, scheme):
    light = shape.index('g')
    if scheme == 'X':
        assert shape[0] == '1'
        weights = [0.0 if i == light else 1.0 for i in range(4)] + [1.0, 0.0]
        zero_loop, tloop, receiver = 5, 4, 0
    else:
        assert shape[3] == '1'
        weights = [0.0 if i == light else 1.0 for i in range(4)] + [0.0, 1.0]
        zero_loop, tloop, receiver = 4, 5, 3
    labels = [letter(ch) for ch in shape] + [letter('y'), letter('x')]
    out = {'A': set(), 'B': set(), 'C': {}, 'D': {}}
    counted = [0]

    def lab(seq):
        word = []
        for i, d in seq:
            word.extend(labels[i] if d == 1 else inverse(labels[i]))
        return tuple(word)

    def adjacent(seq):
        n = len(seq)
        return any({seq[k][0], seq[(k + 1) % n][0]} == {tloop, receiver} for k in range(n))

    def dfs(start, cur, seq, wgt):
        if seq and cur == start and not (seq[-1][0] == seq[0][0] and seq[-1][1] == -seq[0][1]):
            counted[0] += 1
            key = canonical_cyclic(lab(seq))
            adj = adjacent(seq)
            if not key:
                if wgt < 2 and not all(i == zero_loop for i, _ in seq):
                    out['A'].add((wgt, tuple(seq)))
                if adj and wgt < 3:
                    out['B'].add((wgt, tuple(seq)))
            else:
                if wgt < 2:
                    out['C'][key] = min(out['C'].get(key, 9), wgt)
                if adj and wgt < 3:
                    out['D'][key] = min(out['D'].get(key, 9), wgt)
        if len(seq) == MAXLEN:
            return
        for i in range(6):
            for d in (1, -1):
                a, b = (SRC[i], DST[i]) if d == 1 else (DST[i], SRC[i])
                if a != cur or (seq and seq[-1] == (i, -d)):
                    continue
                nw = wgt + weights[i]
                if nw >= 3:
                    continue
                seq.append((i, d))
                dfs(start, b, seq, nw)
                seq.pop()

    for v in '+-':
        dfs(v, v, [], 0.0)
    print('=' * 72)
    print('shape %s scheme %s orders %s weights %s MAXLEN %d closed paths %d'
          % (shape, scheme, ORDERS, weights, MAXLEN, counted[0]))
    print('A. trivial, W < 2, not a pure %s power: %d' % (LOOPNAME[zero_loop], len(out['A'])))
    for wgt, s in sorted(out['A'])[:5]:
        print('   W=%.1f %s' % (wgt, s))
    print('B. trivial, W < 3, receiver-adjacent: %d' % len(out['B']))
    for wgt, s in sorted(out['B'])[:5]:
        print('   W=%.1f %s' % (wgt, s))
    for sec, name in (('C', 'W < 2'), ('D', 'W < 3, receiver-adjacent')):
        keys = sorted(out[sec], key=lambda k: (out[sec][k], len(k), k))
        print('%s. nontrivial labels, %s: %d' % (sec, name, len(keys)))
        for key in keys[:40]:
            print('   W=%.1f  %s' % (out[sec][key], fmt(key)))
        if len(keys) > 40:
            print('   ... %d more' % (len(keys) - 40))

def main():
    for kx, ky in ((2, 2), (3, 3), (2, 3)):
        ORDERS.clear()
        ORDERS.update({'x': kx, 'y': ky})
        for shape, scheme in (('111g', 'X'), ('11g1', 'X'), ('1g11', 'X'),
                              ('g111', 'Y'), ('11g1', 'Y'), ('1g11', 'Y')):
            run(shape, scheme)
    print('LIGHT_END_CLAIM_A_DONE')

if __name__ == '__main__':
    main()
