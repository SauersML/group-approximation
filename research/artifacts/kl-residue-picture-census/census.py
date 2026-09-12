#!/usr/bin/env python3
"""Small-area picture census and short admissible cycles for the length-six KL residue.

Lane kl-curvature-redistribution, 2026-09-12.  Reads the files p_<class>_<area>.txt
written by pairings.c: every reduced (dipole-free), connected, genus-zero pairing of
`area` relator discs, up to relabelling discs of equal orientation.

For each residue shape of `kl-length-six-coincidence-saturated-torsion-residue` and
several loop orders it works in the universal coefficient model

    U = Z(g) * C_ky(y) * C_kx(x)        (None = infinite order),

and reports:
- `spherical`: pairings all of whose faces have trivial label in U (a reduced
  spherical picture over U);
- `candidate`: pairings with at most one nontrivial face (a coefficient-boundary
  picture: the nontrivial face would be the boundary);
- `min_nontrivial`: the fewest nontrivial faces over all pairings, i.e. one more
  than the fewest extra coefficient relations a violation of this area needs.

It also lists the reduced closed paths of length at most four in the star graph
whose label is trivial in U: the admissible regions of degree at most four.
"""
import sys
from collections import Counter

SIGNS = {0: (1, 1, 1, 1, 1, -1), 1: (1, 1, 1, 1, -1, -1)}
NAMES = {0: '+++++-', 1: '++++--'}
SHAPES = {
    0: ['1111', '111g', '11g1', '1g11', 'g111', '11gg', '1g1g', '1gg1'],
    1: ['11g', 'g11', '1gg', 'gg1', 'g1g', 'ggg'],
}
ORDERS = [(2, 2), (2, None), (None, 2), (3, None), (None, 3), (2, 3), (3, 2),
          (3, 3), (4, None), (None, 4), (6, None), (None, 6)]


def letter(ch):
    return () if ch == '1' else ((ch, 1),)


def corner_labels(cls, shape):
    a = [letter(ch) for ch in shape]
    if cls == 0:
        return [a[0], a[1], a[2], a[3], letter('y'), letter('x')]
    return [a[0], a[1], a[2], letter('y'), (), letter('x')]


def inverse(word):
    return tuple((n, -e) for n, e in reversed(word))


def reduce_word(word, orders):
    stack = []
    for n, e in word:
        if stack and stack[-1][0] == n:
            e += stack.pop()[1]
        o = orders.get(n)
        if o:
            e %= o
        if e:
            stack.append((n, e))
    return tuple(stack)


def label(corners, labels):
    word = []
    for i, d in corners:
        word.extend(labels[i] if d == 1 else inverse(labels[i]))
    return tuple(word)


def control_report():
    """Control: with dipoles kept, area two must contain the gluing of w to w^-1.

    That pairing has every face trivial in every coefficient model, so a wrong
    corner or orientation convention shows up as sph = 0 here.
    """
    for cls in (0, 1):
        faces = load_faces(cls, 2, suffix='_dip')
        for shape in SHAPES[cls]:
            labels = corner_labels(cls, shape)
            sph = sum(all(not reduce_word(label(f, labels), {'y': None, 'x': None}) for f in fs)
                      for fs in faces)
            print('control class %s shape %s: %d dipole-kept area-2 pairings, all-trivial %d'
                  % (NAMES[cls], shape, len(faces), sph))
            assert sph >= 1, 'control failed: no all-trivial gluing'
    print('CONTROL_PASS')


def load_faces(cls, area, suffix=''):
    """Return, per pairing, the tuple of face corner sequences."""
    out = []
    half = area // 2
    with open('p_%d_%d%s.txt' % (cls, area, suffix)) as fh:
        for line in fh:
            nums = list(map(int, line.split()))
            assert nums[0] == area
            alpha = nums[1:]
            H = 6 * area
            assert len(alpha) == H
            seen = [False] * H
            faces = []
            for h in range(H):
                if seen[h]:
                    continue
                cyc = []
                x = h
                while not seen[x]:
                    seen[x] = True
                    y = alpha[x]
                    v, j = divmod(y, 6)
                    cyc.append((j, 1) if v < half else ((4 - j) % 6, -1))
                    x = 6 * v + (j + 1) % 6
                faces.append(tuple(cyc))
            assert len(faces) == 2 + 2 * area
            out.append(tuple(faces))
    return out


def star_cycles(cls, maxlen=4):
    s = SIGNS[cls]
    src = ['-' if s[i] == 1 else '+' for i in range(6)]
    dst = ['+' if s[(i + 1) % 6] == 1 else '-' for i in range(6)]
    found = set()

    def canon(seq):
        n = len(seq)
        rev = tuple((i, -d) for i, d in reversed(seq))
        return min(min(seq[k:] + seq[:k] for k in range(n)),
                   min(rev[k:] + rev[:k] for k in range(n)))

    def dfs(start, cur, seq):
        if seq and cur == start:
            if not (seq[-1][0] == seq[0][0] and seq[-1][1] == -seq[0][1]):
                found.add(canon(tuple(seq)))
        if len(seq) == maxlen:
            return
        for i in range(6):
            for d in (1, -1):
                a, b = (src[i], dst[i]) if d == 1 else (dst[i], src[i])
                if a != cur or (seq and seq[-1] == (i, -d)):
                    continue
                seq.append((i, d))
                dfs(start, b, seq)
                seq.pop()

    for v in '+-':
        dfs(v, v, [])
    return sorted(found, key=lambda c: (len(c), c))


def fmt(word):
    return ' '.join(n if e == 1 else '%s^%d' % (n, e) for n, e in word) or '1'


def half_sign(cls, positive, q):
    s = SIGNS[cls]
    return s[q] if positive else -s[5 - q]


def corner_of(positive, q):
    return (q, 1) if positive else ((4 - q) % 6, -1)


def degree_two_options(cls, labels, orders, i):
    """Degree-two faces at corner i of a positive disc D.

    The face has corners (D, i) and (D', q); its arcs are (D, i) <-> (D', q+1) and
    (D, i+1) <-> (D', q).  Arcs join opposite signs, a negative D' must not form a
    dipole (i + q + 1 != 5), and the face label must be trivial in U.
    """
    opts = []
    for positive in (True, False):
        for q in range(6):
            if half_sign(cls, True, i) != -half_sign(cls, positive, (q + 1) % 6):
                continue
            if half_sign(cls, True, (i + 1) % 6) != -half_sign(cls, positive, q):
                continue
            if not positive and (i + (q + 1) % 6) % 6 == 5:
                continue
            if not positive and ((i + 1) % 6 + q) % 6 == 5:
                continue
            word = label(((i, 1), corner_of(positive, q)), labels)
            if not reduce_word(word, orders):
                opts.append((positive, q))
    return opts


def max_degree_two_corners(cls, labels, orders):
    """Largest set of corners of one disc lying in degree-two faces, not all six.

    Consecutive degree-two corners i, i+1 share the arc i+1, so they use the same
    partner orientation with q decreasing by one.  Returns (max count, example).
    """
    opts = [[None] + degree_two_options(cls, labels, orders, i) for i in range(6)]

    def compatible(a, b):
        return a is None or b is None or (a[0] == b[0] and (a[1] - 1) % 6 == b[1])

    best = (0, ())
    for first in opts[0]:
        states = {(first, first is None): (int(first is not None), (first,))}
        for i in range(1, 6):
            nxt = {}
            for (prev, gap), (count, path) in states.items():
                for o in opts[i]:
                    if not compatible(prev, o):
                        continue
                    key = (o, gap or o is None)
                    val = (count + (o is not None), path + (o,))
                    if key not in nxt or val[0] > nxt[key][0]:
                        nxt[key] = val
            states = nxt
        for (last, gap), (count, path) in states.items():
            if gap and compatible(last, first) and count > best[0]:
                best = (count, tuple(i for i in range(6) if path[i] is not None))
    return best


def canonical_cyclic(word, orders):
    """Cyclically reduced form, minimized over rotations and inversion."""
    w = list(reduce_word(word, orders))
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        e = w[0][1] + w[-1][1]
        o = orders.get(w[0][0])
        if o:
            e %= o
        name = w[0][0]
        w = w[1:-1]
        if e:
            w = [(name, e)] + w
        w = list(reduce_word(w, orders))
    if not w:
        return ()
    cands = []
    for seq in (w, list(reduce_word(inverse(tuple(w)), orders))):
        for k in range(len(seq)):
            rot = seq[k:] + seq[:k]
            cands.append(tuple((n, e % orders[n] if orders.get(n) else e) for n, e in rot))
    return min(cands)


def low_weight_cycles(cls, shape, weights, orders, bound, maxlen=8):
    """Reduced closed star-graph paths of weight below `bound`, with labels.

    `weights` gives theta per corner index 0..5.  Returns a dict
    canonical label -> (min weight, has heavy step, has loop step).
    """
    s = SIGNS[cls]
    labels = corner_labels(cls, shape)
    src = ['-' if s[i] == 1 else '+' for i in range(6)]
    dst = ['+' if s[(i + 1) % 6] == 1 else '-' for i in range(6)]
    loops = {i for i in range(6) if src[i] == dst[i]}
    out = {}

    def dfs(start, cur, seq, weight):
        if seq and cur == start and not (seq[-1][0] == seq[0][0] and seq[-1][1] == -seq[0][1]):
            key = canonical_cyclic(label(tuple(seq), labels), orders)
            heavy = any(weights[i] >= 1 and i not in loops for i, _ in seq)
            loop = any(i in loops for i, _ in seq)
            prev = out.get(key)
            if prev is None or weight < prev[0] or (weight == prev[0] and (heavy and loop) and not (prev[1] and prev[2])):
                out[key] = (weight, heavy, loop)
        if len(seq) == maxlen:
            return
        for i in range(6):
            for d in (1, -1):
                a, b = (src[i], dst[i]) if d == 1 else (dst[i], src[i])
                if a != cur or (seq and seq[-1] == (i, -d)):
                    continue
                nw = weight + weights[i]
                if nw >= bound:
                    continue
                seq.append((i, d))
                dfs(start, b, seq, nw)
                seq.pop()

    for v in '+-':
        dfs(v, v, [], 0.0)
    return out


def claim_a_report():
    """Cross-check Claim A of the involution-loop curvature route."""
    orders = {'y': 2, 'x': 2}
    for shape, light in (('11g1', 2), ('1g11', 1)):
        weights = [1.0, 1.0, 1.0, 1.0, 0.5, 0.5]
        weights[light] = 0.0
        found = low_weight_cycles(0, shape, weights, orders, 2.5)
        print('claimA shape', shape, 'cycles of weight < 5/2 (canonical label: weight, heavy, loop)')
        for key in sorted(found, key=lambda k: (found[k][0], k)):
            wgt, heavy, loop = found[key]
            if wgt < 2 or (heavy and loop):
                print('   W=%.1f heavy=%d loop=%d  label=%s' % (wgt, heavy, loop, fmt(key)))


def main():
    claim_a_report()
    for cls in (0, 1):
        print('=' * 70)
        print('class', NAMES[cls])
        faces_by_area = {area: load_faces(cls, area) for area in (2, 4)}
        for area in (2, 4):
            print('  area %d: %d reduced planar pairings (up to relabelling)'
                  % (area, len(faces_by_area[area])))
        cycles = star_cycles(cls)
        for shape in SHAPES[cls]:
            labels = corner_labels(cls, shape)
            print('-' * 70)
            print('shape', shape)
            for ky, kx in ORDERS:
                orders = {'y': ky, 'x': kx}
                adm = [c for c in cycles if not reduce_word(label(c, labels), orders)]
                short = Counter(len(c) for c in adm)
                parts = []
                for area in (2, 4):
                    cache = {}
                    spherical = candidate = 0
                    minimal = None
                    for faces in faces_by_area[area]:
                        k = 0
                        for f in faces:
                            if f not in cache:
                                cache[f] = bool(reduce_word(label(f, labels), orders))
                            k += cache[f]
                        spherical += k == 0
                        candidate += k <= 1
                        minimal = k if minimal is None else min(minimal, k)
                    parts.append('A%d sph=%d cand=%d min_nontriv=%s'
                                 % (area, spherical, candidate, minimal))
                m2 = max_degree_two_corners(cls, labels, orders)
                print('  orders y=%s x=%s | adm cycles len2=%d len3=%d len4=%d | maxdeg2 %d at %s | %s'
                      % (ky or 'inf', kx or 'inf', short[2], short[3], short[4],
                         m2[0], m2[1], ' | '.join(parts)))
            # Show the admissible short cycles for involution loops.
            orders = {'y': 2, 'x': 2}
            for c in cycles:
                if len(c) <= 3 and not reduce_word(label(c, labels), orders):
                    print('    inv-loops admissible:', c, '~', fmt(label(c, labels)))
    print('KLCR_CENSUS_PY_DONE')


if __name__ == '__main__':
    main()
