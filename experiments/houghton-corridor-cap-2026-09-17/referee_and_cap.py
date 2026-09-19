#!/usr/bin/env python3
"""Independent referee check of houghton-h3-at-least-cubic-dehn-corridor-proof,
plus a numerical sanity check of the distortion bound (Lemma D) used in
houghton-hnn-corridor-lower-bounds-cap-at-base-distortion.

Written from scratch (does not import the wave-13 scripts).
Right actions: a word is applied letter by letter, left to right.
Points are (r, p), r in {1,2,3}, p >= 1.
Letters: 'X','x' = lambda_(1,2)^(+-1); 'Y','y' = lambda_(1,3)^(+-1); 'a' = alpha.
"""
import random, sys

def lam(a, b, z):
    r, p = z
    if r == a:
        return (a, p - 1) if p >= 2 else (b, 1)
    if r == b:
        return (b, p + 1)
    return z

def laminv(a, b, z):
    r, p = z
    if r == b:
        return (b, p - 1) if p >= 2 else (a, 1)
    if r == a:
        return (a, p + 1)
    return z

def act(letter, z):
    if letter == 'X': return lam(1, 2, z)
    if letter == 'x': return laminv(1, 2, z)
    if letter == 'Y': return lam(1, 3, z)
    if letter == 'y': return laminv(1, 3, z)
    if letter == 'a':
        if z == (1, 1): return (1, 2)
        if z == (1, 2): return (1, 1)
        return z
    raise ValueError(letter)

def apply(word, z):
    for c in word:
        z = act(c, z)
    return z

INV = {'X': 'x', 'x': 'X', 'Y': 'y', 'y': 'Y', 'a': 'a'}
def inverse(word):
    return ''.join(INV[c] for c in reversed(word))

def pts(R):
    return [(r, p) for r in (1, 2, 3) for p in range(1, R + 1)]

def equal(w1, w2, R):
    # both sides are eventually uniform translations beyond depth |w|+3,
    # so agreement on depth <= R with R > max(|w1|,|w2|)+3 suffices
    return all(apply(w1, z) == apply(w2, z) for z in pts(R))

def tau(word):
    return word.count('Y') - word.count('y')

def fixes_ray3(word):
    R = len(word) + 5
    return all(apply(word, (3, p)) == (3, p) for p in range(1, R + 1))

def Lcoord(z):
    r, p = z
    assert r in (1, 2)
    return p if r == 1 else 1 - p

def inv_count(word):
    """inversions on L = ray2 u ray1 of an element fixing ray 3."""
    R = 3 * len(word) + 10
    dom = [(2, q) for q in range(R, 0, -1)] + [(1, p) for p in range(1, R + 1)]
    img = [Lcoord(apply(word, z)) for z in dom]
    # outside the window the element is an order-preserving shift, and
    # displacement <= |word|, so all inversions lie inside the window
    n = 0
    for i in range(len(img)):
        for j in range(i + 1, len(img)):
            if img[i] > img[j]:
                n += 1
    return n

def check_identities():
    ok1 = equal('YXy', 'aX', 12)
    ok2 = equal('Yay', 'Xax', 12)
    return ok1, ok2

def check_wm(m):
    g = 'Y' * m + 'X' * m + 'y' * m
    w = inverse(g) + 'a' + g + 'a'
    assert len(w) == 6 * m + 2
    assert equal(w, '', len(w) + 5), 'w_m not trivial'
    ypos = [i for i, c in enumerate(w) if c in 'Yy']
    admissible = {}
    for s in range(len(ypos)):
        for t in range(s + 1, len(ypos)):
            i, j = ypos[s], ypos[t]
            if w[i] == w[j]:
                continue  # same sign: excluded by the orientation lemma
            arc = w[i + 1:j]
            if tau(arc) == 0 and fixes_ray3(arc):
                admissible.setdefault(i, []).append(j)
                admissible.setdefault(j, []).append(i)
    # forced matching: every a_i has exactly one admissible partner, a b-letter
    blocks = {}
    names = 'ABCD'
    for k, i in enumerate(ypos):
        blocks[i] = names[k // m] + str(k % m + 1)
    total = 0
    matched = {}
    # Build the forced matching as in Step 3 and check uniqueness
    for i in ypos:
        if blocks[i][0] == 'A':
            parts = admissible.get(i, [])
            assert len(parts) == 1 and blocks[parts[0]][0] == 'B', (m, blocks[i], [blocks[p] for p in parts])
            matched[i] = parts[0]
    usedB = set(matched.values())
    assert len(usedB) == m
    for i in ypos:
        if blocks[i][0] == 'C':
            parts = [j for j in admissible.get(i, []) if j not in usedB]
            assert len(parts) == 1 and blocks[parts[0]][0] == 'D', (m, blocks[i])
            matched[i] = parts[0]
    for i, j in matched.items():
        total += inv_count(w[i + 1:j])
    return total

# ---------- Lemma D sanity: B-length of elements of B = Stab(ray 3) ----------
def bword_for(word):
    """Explicit word in X^{+-1}, alpha for an element b of B given as an H_3 word.
    Construction of Lemma D: undo the L-translation by X^t, then bubble-sort
    the finitary remainder with passes of adjacent transpositions s_i."""
    l = len(word)
    t = Lcoord(apply(word, (1, l + 5))) - (l + 5)   # eventual shift on L
    # b = sigma * shift_t with sigma finitary; X shifts L by -1 (right action)
    corr = ('X' * t) if t > 0 else ('x' * (-t))
    full = word + corr                               # finitary on L
    W = 2 * l + 8
    dom = list(range(-W, W + 1))
    def toz(c):
        return (1, c) if c >= 1 else (2, 1 - c)
    perm = {c: Lcoord(apply(full, toz(c))) for c in dom}
    assert all(perm[c] == c for c in dom if abs(c) > l + 4), 'not finitary in window'
    # bubble sort the sequence perm[-W..W] to identity; record swaps at positions
    seq = [perm[c] for c in dom]
    swaps = []
    changed = True
    while changed:
        changed = False
        for k in range(len(seq) - 1):
            if seq[k] > seq[k + 1]:
                seq[k], seq[k + 1] = seq[k + 1], seq[k]
                swaps.append(dom[k])  # swap L-coords dom[k], dom[k]+1
                changed = True
    # s_c = transposition of L-coords c, c+1 = alpha^{X^{-(c-1)}}... compute
    # conjugator: alpha swaps coords 1,2 ; X shifts coord by -1, so
    # x^{k} a X^{k}... we just build and verify numerically.
    def s(c):
        k = c - 1  # need coords 1,2 -> c, c+1 : conjugate by shift +k = X^{-k}
        pre = ('X' * k) if k > 0 else ('x' * (-k))
        return pre + 'a' + inverse(pre)
    # element sigma (finitary) equals product of swaps applied in reverse
    # order; the B-word for sigma^{-1}... build and verify directly.
    cand = ''.join(s(c) for c in swaps)
    cand = freereduce(cand)
    bw = freereduce(inverse(cand) + inverse(corr)) if False else None
    # sigma = full; sorting means full * (product of swaps as right actions)
    # rearranges images; verify by trying both orders.
    for trial in (cand, inverse(cand)):
        b = freereduce(trial + inverse(corr))
        if equal_on_L(b, word, W):
            return b
    raise AssertionError('construction failed')

def freereduce(w):
    out = []
    for c in w:
        if out and INV[c] == out[-1] and c != 'a':
            out.pop()
        elif out and c == 'a' and out[-1] == 'a':
            out.pop()
        else:
            out.append(c)
    return ''.join(out)

def equal_on_L(w1, w2, R):
    return all(apply(w1, z) == apply(w2, z) for z in pts(R + 5))

def random_B_element(l):
    a = random.randint(0, l // 3)
    u = ''.join(random.choice('Xxa') for _ in range(l - 2 * a))
    return 'Y' * a + u + 'y' * a

if __name__ == '__main__':
    random.seed(20260919)
    print('identities 1a:', check_identities())
    for m in range(2, int(sys.argv[1]) if len(sys.argv) > 1 else 13):
        tot = check_wm(m)
        print('m', m, 'len', 6 * m + 2, 'forced matching unique; sum inv', tot,
              'm^2(m-1) =', m * m * (m - 1), 'OK' if tot == m * m * (m - 1) else 'MISMATCH')
    print('Lemma D sanity (B-length of constructed word vs H3-length l):')
    for l in (6, 10, 16, 24, 32):
        worst = 0.0
        for _ in range(8):
            w = random_B_element(l)
            assert fixes_ray3(w)
            b = bword_for(w)
            worst = max(worst, len(b) / l ** 2)
        # also the distorted family h_k with k=m=l/3
        k = l // 3
        h = 'Y' * k + 'x' * k + 'y' * k
        bh = bword_for(h)
        print('  l', l, 'max |b|_B / l^2 over random', round(worst, 3),
              '| h_k: inv', inv_count(h), ' |constructed|', len(bh), ' /l^2', round(len(bh) / l ** 2, 3))
