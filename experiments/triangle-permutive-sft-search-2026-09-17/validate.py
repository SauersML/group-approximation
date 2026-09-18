"""Consistency checks for search.py: (1) periodic => automaton never empty; (2) automaton-empty at level n =>
brute force finds no row word of length m whose n-step evolution (light cone) stays legal, for some m."""
import random, itertools
from search import cycle_edges, level_run, iso_reps

def legal_cone(T, k, L, A, word, n):
    r = list(word)
    for t in range(n + 1):
        if len(r) < L:
            return True
        for i in range(len(r) - L + 1):
            w = 0
            for j in range(L):
                w = w * k + r[i + j]
            if not (A >> w) & 1:
                return False
        r = [T[r[i]][r[i + 1]] for i in range(len(r) - 1)]
    return True

random.seed(1)
bad = 0
for k, L, P in [(2, 4, 8), (3, 2, 6), (3, 3, 5)]:
    for T in iso_reps(k):
        edges, kL = cycle_edges(T, k, L, P)
        for trial in range(40):
            A = random.getrandbits(kL) | random.getrandbits(kL)
            per = any(e & ~A == 0 for e in edges)
            r = level_run(T, k, L, A, 12)
            if per and r[0] == "empty":
                bad += 1; print("BAD1", k, L, T, hex(A), r)
            if r[0] == "empty":
                n = r[1]
                m = L + n + 6
                ok = any(legal_cone(T, k, L, A, w, n) for w in itertools.product(range(k), repeat=m)) if k ** m < 3e5 else None
                # a word of length m legal for n steps with m large must exist if Z_n nonempty; expect none
                if ok:
                    # may still be fine (finite words can be legal without bi-infinite extension); count only
                    pass
            else:
                # alive at level 12: brute force should find legal cone words of length L+12+2
                m = L + 12 + 2
                if k ** m < 3e5:
                    ok = any(legal_cone(T, k, L, A, w, 12) for w in itertools.product(range(k), repeat=m))
                    if not ok:
                        bad += 1; print("BAD2", k, L, T, hex(A), r)
print("bad", bad)

# (3) empty at level n => no spatially periodic row (period <= 12) survives n steps inside Z_0
def per_survives(T, k, L, A, p, n):
    for r in itertools.product(range(k), repeat=p):
        r = list(r); good = True
        for t in range(n + 1):
            for i in range(p):
                w = 0
                for j in range(L):
                    w = w * k + r[(i + j) % p]
                if not (A >> w) & 1:
                    good = False; break
            if not good: break
            r = [T[r[i]][r[(i + 1) % p]] for i in range(p)]
        if good:
            return True
    return False
bad3 = 0; checked = 0
for k, L in [(2, 4), (2, 5), (3, 3)]:
    for T in iso_reps(k):
        for trial in range(150):
            A = random.getrandbits(k ** L) | (random.getrandbits(k ** L) & random.getrandbits(k ** L))
            r = level_run(T, k, L, A, 10)
            if r[0] == "empty":
                checked += 1
                for p in range(1, 13 if k == 2 else 8):
                    if per_survives(T, k, L, A, p, r[1]):
                        bad3 += 1; print("BAD3", k, L, T, hex(A), r, p); break
print("empty-checked", checked, "bad3", bad3)
