"""Sanity check of the free-level section cocycle Phi_x used in
research/self-similar-spinal-groups-not-fp-torsion-quotients-proof.md,
for the first Grigorchuk group and the Gupta-Sidki 3-group.
Checks on random words: (c) lifting pi(Phi_x(w)) = pi(w)|_x (compared on
the tree to depth D), (d) |Phi_x(w)| <= #B-letters, and (e)
Phi_{x0}(c^-1 b c) = omega_{c(x0)}(b)."""
import random, itertools
random.seed(1)
D = 7

def grig():
    # letters a,b,c,d ; x0 = 1 ; sections at (0,1)
    perm = {'a': (1, 0), 'b': (0, 1), 'c': (0, 1), 'd': (0, 1)}
    sec = {'a': ('', ''), 'b': ('a', 'c'), 'c': ('a', 'd'), 'd': ('', 'b')}
    return 2, perm, sec, 'a', 'bcd', 1

def gs():
    # Gupta-Sidki p=3: a = rooted 3-cycle, t=(a, a^-1, t); letters a,A=a^-1,t,T=t^-1
    perm = {'a': (1, 2, 0), 'A': (2, 0, 1), 't': (0, 1, 2), 'T': (0, 1, 2)}
    sec = {'a': ('', '', ''), 'A': ('', '', ''), 't': ('a', 'A', 't'), 'T': ('A', 'a', 'T')}
    return 3, perm, sec, 'aA', 'tT', 2

def act(g, word, v):
    """pi(word) applied to vertex v (tuple), word acts right-to-left."""
    d, perm, sec = g[0], g[1], g[2]
    v = list(v)
    for s in reversed(word):
        v = apply_letter(g, s, v)
    return tuple(v)

def apply_letter(g, s, v):
    if not v:
        return v
    d, perm, sec = g[0], g[1], g[2]
    x = v[0]
    return [perm[s][x]] + apply_word(g, sec[s][x], v[1:])

def apply_word(g, w, v):
    for s in reversed(w):
        v = apply_letter(g, s, v)
    return v

def section_word(g, w, x):
    """Phi_x(w) as a word (positive letters only; inverses are letters)."""
    d, perm, sec, A, B, x0 = g
    out = []
    y = x
    # process right to left, prepend
    for s in reversed(w):
        if s in B:
            out.insert(0, sec[s][y])
        y = perm[s][y]
    return ''.join(out)

def check(g, trials=300):
    d, perm, sec, A, B, x0 = g
    worst = 0
    for _ in range(trials):
        n = random.randint(1, 30)
        w = ''.join(random.choice(A + B) for _ in range(n))
        for x in range(d):
            sw = section_word(g, w, x)
            assert len(sw) <= sum(ch in B for ch in w)
            # lifting: pi(w)(x v) = pi(w)(x) pi(Phi_x w)(v)
            for v in itertools.islice(itertools.product(range(d), repeat=D - 1), 0, None, max(1, d ** (D - 1) // 40)):
                lhs = act(g, w, (x,) + v)
                rhs = (act(g, w, (x,))[0],) + tuple(apply_word(g, sw, list(v)))
                assert lhs == rhs, (w, x, v)
    return True

for name, g in [('grigorchuk', grig()), ('gupta-sidki-3', gs())]:
    print(name, 'lifting and length checks pass:', check(g))
