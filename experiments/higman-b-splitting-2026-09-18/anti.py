"""Infinite-order certificates in the action of B = <b,d> on the edges of T_B.

Gamma(3,m) = A.B exactly (A = <a,c>, B = <b,d>, A cap B = 1), so edges of T_B = Gamma/B <-> A-words,
and beta in B acts on A-words by  beta * alpha = alpha' * beta'  (syllable by syllable; the
"section" of beta at a prefix is the B-word left over).  G_s = image of B acting on the A-words
whose first syllable is a power of s (s in {a,c}); this is a quotient of B/Lambda_B.

Lemma.  Let g in B, v an A-word starting with s, of even syllable length (so words below v start
with s again), whose <g>-orbit has exact size N >= 2, and suppose the section of g^N at v is
conjugate in B to g or g^-1.  Then g has infinite order in G_s, hence B/Lambda_B is infinite and
Gamma(3,m) acts non-discretely on T_B (Gamma is an irreducible lattice).
Proof: if ord(g) = k < oo in G_s then N | k, ord(g^N) = k/N, and the section map on Stab(v) is a
homomorphism into G_s, so k = ord(section) <= k/N < k.

usage: python3 anti.py e maxlen depth"""
import sys, itertools
e = int(sys.argv[1]); maxlen = int(sys.argv[2]); depth = int(sys.argv[3]) if len(sys.argv) > 3 else 0
sys.argv = [sys.argv[0], str(e), '1']
from pathstab import push, red, inv, m

def left(s, word, j):
    """word * s^j = s^j' * word'  (word in B)."""
    w2, i2 = push(s, -j, inv(word))
    return (-i2) % m, inv(w2)

def cyc(w):
    """cyclic reduction of a B-word (tuple of (letter, exp))."""
    w = list(w)
    while len(w) >= 2 and w[0][0] == w[-1][0]:
        g = w[0][0]; x = (w[0][1] + w[-1][1]) % m
        w = w[1:-1]
        if x: w = [(g, x)] + w
    return tuple(w)

def conj_class(w):
    c = cyc(w); L = len(c)
    return {c[i:] + c[:i] for i in range(max(L, 1))}

def section_power(h, s, x):
    """orbit size n of s^x under h, and the section of h^n at s^x."""
    y = x; secs = []
    while True:
        y, w = left(s, h, y); secs.append(w)
        if y == x: break
    sec = ()
    for w in secs:            # h^n s^x = s^x w_n ... w_1
        sec = red(list(w) + list(sec))
    return len(secs), sec

def orbit_reps(h, s):
    seen = set(); reps = []
    for x in range(1, m):
        if x in seen: continue
        y = x; reps.append(x)
        while True:
            seen.add(y); y = left(s, h, y)[0]
            if y == x: break
    return reps

other = {'a': 'c', 'c': 'a'}

def search(g, s0, cap):
    targets = conj_class(g) | conj_class(inv(g))
    stack = [(g, s0, 0, 1, ())]
    while stack:
        h, s, dep, N, path = stack.pop()
        if dep > 0 and dep % 2 == 0 and N >= 2 and cyc(h) in targets:
            return N, path, h
        if dep == depth: continue
        for x in orbit_reps(h, s):
            n, sec = section_power(h, s, x)
            if len(sec) > cap or len(sec) == 0: continue
            stack.append((sec, other[s], dep + 1, N * n, path + ((s, x, n),)))
    return None

def bwords(L):
    for start in 'bd':
        letters = [start if k % 2 == 0 else ('d' if start == 'b' else 'b') for k in range(L)]
        for exps in itertools.product(range(1, m), repeat=L):
            w = tuple(zip(letters, exps))
            if cyc(w) == w: yield w

if __name__ == '__main__':
    hits = 0
    for L in range(1, maxlen + 1):
        tried = 0
        for g in bwords(L):
            tried += 1
            for s0 in 'ac':
                r = search(g, s0, 2 * L + 2)
                if r:
                    hits += 1
                    print('e=%d g=%s half=%s orbit N=%d path=%s section=%s' % (e, g, s0, r[0], r[1], r[2]))
                    sys.stdout.flush()
                    if hits >= 3: sys.exit(0)
        print('e=%d length %d: %d words tried, certificates so far %d' % (e, L, tried, hits)); sys.stdout.flush()
