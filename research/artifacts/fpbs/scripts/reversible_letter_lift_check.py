# Sanity check for step 4 of research/fpbs-reversible-letter-nonunimodular-proof.md.
# Run: python3 reversible_letter_lift_check.py (a few seconds; run on MSI 2026-09-12).
# Expected: 0 bad edges in the four symmetric cases, and a positive count for every
# shift in the control that reverses D_a = {0,1,3}.
# Sanity check of the height-compensated lift on tree-projected Cayley graphs of F_2 x Z.
# A random color-preserving automorphism sigma of a ball in Cay(F_2,{a,b}) keeps the orientation
# of every letter outside `rev` and may reverse letters in `rev`.  Reversing an s-edge shifts the
# height potential by -c_s, where D_s = c_s - D_s.  Check that every horizontal edge of the ball
# maps to an edge.  Vertical edges are preserved by any height shift that is constant on fibres.
import random

LET = ['a', 'A', 'b', 'B']
def inv(x): return x.swapcase()
def mul(w, x): return w[:-1] if w and w[-1] == inv(x) else w + x

def ball(R):
    words, frontier = [''], ['']
    for _ in range(R):
        frontier = [w + x for w in frontier for x in LET if not (w and w[-1] == inv(x))]
        words += frontier
    return words

def flip_or_keep(c, rev):
    return (c.upper(), c) if (c in rev and random.random() < 0.5) else (c, c.upper())

def random_aut(R, rev):
    img, lm = {'': ''}, {'': {}}
    for c in 'ab':
        lm[''][c], lm[''][c.upper()] = flip_or_keep(c, rev)
    for w in ball(R):
        if not w:
            continue
        p, x = w[:-1], w[-1]
        y = lm[p][x]
        img[w] = mul(img[p], y)
        m = {inv(x): inv(y), x: y}
        for c in 'ab':
            if c != x.lower():
                m[c], m[c.upper()] = flip_or_keep(c, rev)
        lm[w] = m
    return img, lm

def potential(R, lm, cs):
    h = {'': 0}
    for w in ball(R):
        if not w:
            continue
        p, x = w[:-1], w[-1]
        s = x.lower()
        reversed_ = lm[p][x] != x
        # oriented edge p -> w if x positive, w -> p if x negative; reversal shifts by -c_s
        if x == s:
            h[w] = h[p] + (-cs[s] if reversed_ else 0)
        else:
            h[w] = h[p] + (cs[s] if reversed_ else 0)
    return h

def check(D, rev, R=5, trials=40):
    cs = {}
    for s in rev:
        c = max(D[s]) + min(D[s])
        assert {c - d for d in D[s]} == set(D[s]), (s, D[s])
        cs[s] = c
    for s in 'ab':
        cs.setdefault(s, 0)
    bad = 0
    words = ball(R)
    for _ in range(trials):
        img, lm = random_aut(R, rev)
        h = potential(R, lm, cs)
        for g in words:
            for s in 'ab':
                gs = mul(g, s)
                if len(gs) > R:
                    continue
                t = next(z for z in LET if mul(img[g], z) == img[gs])
                allowed = set(D[t]) if t == t.lower() else {-d for d in D[t.lower()]}
                for d in D[s]:
                    if d + h[gs] - h[g] not in allowed:
                        bad += 1
    return bad

cases = [
    ("G1 D_a={0,1}, D_b={0}, reverse b only", {'a': [0, 1], 'b': [0]}, 'b'),
    ("G1 D_a={0,1}, D_b={0}, reverse a and b", {'a': [0, 1], 'b': [0]}, 'ab'),
    ("D_a={0,1,3}, D_b={0}, reverse b only", {'a': [0, 1, 3], 'b': [0]}, 'b'),
    ("D_a={0,2,3,5}, D_b={1,4}, reverse a and b", {'a': [0, 2, 3, 5], 'b': [1, 4]}, 'ab'),
]
random.seed(20260912)
for name, D, rev in cases:
    print(f"{name}: bad edges = {check(D, rev)}")
# negative control: D_a={0,1,3} is not symmetric up to translation; reversing a must break edges
def check_forced(D, rev, cs):
    random.seed(7)
    words, bad = ball(4), 0
    for _ in range(20):
        img, lm = random_aut(4, rev)
        h = potential(4, lm, cs)
        for g in words:
            gs = mul(g, 'a')
            if len(gs) > 4:
                continue
            t = next(z for z in LET if mul(img[g], z) == img[gs])
            allowed = set(D[t]) if t == t.lower() else {-d for d in D[t.lower()]}
            bad += sum(1 for d in D['a'] if d + h[gs] - h[g] not in allowed)
    return bad
for c in range(-4, 5):
    print(f"control D_a={{0,1,3}} reversed with shift {c}: bad edges = {check_forced({'a': [0, 1, 3], 'b': [0]}, 'a', {'a': c, 'b': 0})}")
