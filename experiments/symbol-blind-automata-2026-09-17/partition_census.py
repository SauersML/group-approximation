"""Census of injective symbol-blind (S_A-equivariant) automata on finite groups.

For |A| >= |M|+2 an S_A-equivariant local rule is a selector: tau(x)(g) = x(g*sigma(pi_g x)),
sigma choosing one class of the partition pi_g x of M.  tau_q is bijective on A^G (G finite)
iff the partition map T(P) = psi_P^* P permutes Part_{<=q}(G) and psi_P hits every class
(see research/symbol-blind-automata-reduce-to-defect-counting-proof.md).  With q >= |G| every
partition is realised, so we test all set partitions of G.

Usage: python3 partition_census.py <group> <M as comma list>
  group: Z<n> (cyclic) or Z2xZ<n> (elements (a,b) encoded a*n+b) or S3
Prints the number of rules with sigma(discrete)=e and how many are bijective, with the
non-identity bijective ones listed by their sigma table.
"""
import itertools, sys
import numpy as np

def group(name):
    if name == 'S3':
        els = list(itertools.permutations(range(3)))
        idx = {p: i for i, p in enumerate(els)}
        return len(els), lambda a, b: idx[tuple(els[a][els[b][i]] for i in range(3))]
    if name.startswith('Z2xZ'):
        n = int(name[4:]); N = 2 * n
        return N, lambda a, b: ((a // n + b // n) % 2) * n + (a % n + b % n) % n
    n = int(name[1:]); return n, lambda a, b: (a + b) % n

def set_partitions(n):  # restricted growth strings
    def rec(prefix, m):
        if len(prefix) == n:
            yield tuple(prefix); return
        for c in range(m + 1):
            yield from rec(prefix + [c], max(m, c + 1))
    yield from rec([0], 1)

def canon(t):
    d = {}; return tuple(d.setdefault(v, len(d)) for v in t)

def main():
    N, mul = group(sys.argv[1]); M = [int(s) for s in sys.argv[2].split(',')]
    k = len(M); assert M[0] == 0
    pats = sorted(set(canon(p) for p in itertools.product(range(k), repeat=k)))
    pid = {p: i for i, p in enumerate(pats)}
    # choices per pattern: representative index (first position) of each class
    choices = [[p.index(c) for c in range(max(p) + 1)] for p in pats]
    disc = pid[tuple(range(k))]
    parts = np.array(list(set_partitions(N)), dtype=np.int16)
    ncls = parts.max(axis=1) + 1
    W = np.zeros((len(parts), N), dtype=np.int32)
    for r, P in enumerate(parts):
        for g in range(N):
            W[r, g] = pid[canon([P[mul(g, m)] for m in M])]
    free = [i for i in range(len(pats)) if len(choices[i]) > 1 and i != disc]
    mtab = np.array([[mul(g, m) for m in M] for g in range(N)])
    pairs = [(g, h) for g in range(N) for h in range(g + 1, N)]
    gi = np.array([p[0] for p in pairs]); hi = np.array([p[1] for p in pairs])
    weights = (1 << np.arange(len(pairs), dtype=np.int64))
    total = 0; good = []
    rows = np.arange(len(parts))[:, None]
    for combo in itertools.product(*[range(len(choices[i])) for i in free]):
        total += 1
        off = np.zeros(len(pats), dtype=np.int32)
        for i, c in zip(free, combo):
            off[i] = choices[i][c]
        psi = mtab[np.arange(N)[None, :], off[W]]
        TV = parts[rows, psi]
        srt = np.sort(TV, axis=1)
        hit = 1 + (np.diff(srt, axis=1) != 0).sum(axis=1)
        if not np.all(hit == ncls):
            continue
        code = ((TV[:, gi] == TV[:, hi]).astype(np.int64) * weights).sum(axis=1)
        if len(np.unique(code)) == len(parts):
            good.append(combo)
    print(sys.argv[1], M, 'rules', total, 'bijective', len(good))
    for combo in good:
        if any(off_c != 0 for off_c in [choices[i][c] for i, c in zip(free, combo)]):
            print('  nonidentity sigma:', {pats[i]: M[choices[i][c]] for i, c in zip(free, combo) if choices[i][c] != 0})

if __name__ == '__main__':
    main()
