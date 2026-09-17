"""Check of the coset obstruction on random words and permutation roots.

For a root tau of wbar over F <= S_n, Gamma = <F, tau>:
  (1) D*(tau - 1) maps to 0 in Z[Gamma/F]  (Fox fundamental formula at a root);
  (2) rank of right multiplication by D on Q[Gamma] is at most |Gamma| - [Gamma:F] + 1,
      checked here as rank mod a large prime (which is <= the rational rank);
  (3) the bound is attained on the sample (reported), and no root with Gamma != F is a unit.
Usage: python3 cosetbound.py SEED TRIALS
"""
import itertools, random, sys, time
import numpy as np
from regroots import mul, inv, ident, closure, evalword, random_word, rank_modp, fmt

def fox_terms(word, tb, n):
    out = []; u = ident(n); ti = inv(tb)
    for kind, v in word:
        if kind == 'g':
            u = mul(u, v)
        elif v == 1:
            out.append((1, u)); u = mul(u, tb)
        else:
            u = mul(u, ti); out.append((-1, u))
    return out

def run(F, n, rng, trials, cap=720):
    e = ident(n); Fset = set(F)
    gens = [g for g in F if g != e]
    stats = {'roots': 0, 'proper': 0, 'fox_ok': 0, 'bound_ok': 0, 'bound_attained': 0, 'units_in_F': 0, 'roots_in_F': 0}
    perms = list(itertools.permutations(range(n)))
    for _ in range(trials):
        w = random_word(F, rng.choice([2, 3, 4, 5]), rng)
        for tb in rng.sample(perms, 400):
            if evalword(w, tb, n) != e:
                continue
            elems, idx = closure(gens + [tb], n, cap)
            if elems is None:
                continue
            stats['roots'] += 1
            N = len(elems); terms = fox_terms(w, tb, n)
            # cosets gF
            coset = {}
            for g in elems:
                key = min(mul(g, f) for f in F)
                coset.setdefault(key, len(coset))
            cid = {g: coset[min(mul(g, f) for f in F)] for g in elems}
            vec = {}
            for eps, s in terms:
                for sgn, x in ((1, mul(s, tb)), (-1, s)):
                    vec[cid[x]] = vec.get(cid[x], 0) + eps * sgn
            if all(v == 0 for v in vec.values()):
                stats['fox_ok'] += 1
            M = np.zeros((N, N), dtype=np.int64)
            for x, gx in enumerate(elems):
                for eps, s in terms:
                    M[x, idx[mul(gx, s)]] += eps
            r = rank_modp(M, 32749)
            bound = N - len(coset) + 1
            stats['bound_ok'] += (r <= bound)
            stats['bound_attained'] += (r == bound)
            if N == len(F):
                stats['roots_in_F'] += 1
                stats['units_in_F'] += (r == N)
            else:
                stats['proper'] += 1
    return stats

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed); n = 6; e = ident(n)
    S3 = []
    for p in itertools.permutations(range(3)):
        S3.append(tuple(list(p) + [3, 4, 5]))
    C2 = [e, (1, 0, 2, 3, 4, 5)]
    C3 = [e, (1, 2, 0, 3, 4, 5), (2, 0, 1, 3, 4, 5)]
    for name, F in (('C2', C2), ('C3', C3), ('S3', S3)):
        t0 = time.time()
        print(name, run(F, n, rng, trials), 'time %.1f' % (time.time() - t0), flush=True)
