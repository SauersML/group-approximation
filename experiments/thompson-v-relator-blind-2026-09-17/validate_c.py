"""Brute-force check of census.c_choices: every involution c on [m] with (ac)^3=1."""
import itertools, sys
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
import census as C

def brute(a):
    m = len(a); out = set()
    for c in itertools.permutations(range(m)):
        if all(c[c[i]] == i for i in range(m)):
            ac = [c[a[i]] for i in range(m)]
            if all(ac[ac[ac[i]]] == i for i in range(m)):
                out.add(tuple(c))
    return out

for m in range(1, 9):
    for combo in C.s4_sets(m):
        a, b = C.glue(combo)
        got = C.c_choices(a)
        assert len(got) == len(set(got)), 'duplicates'
        assert set(got) == brute(a), (m, combo)
    print('m', m, 'ok', flush=True)
