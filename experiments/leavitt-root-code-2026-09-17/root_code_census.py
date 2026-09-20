"""Root-code census for finite matrix shadows of the negative Cuntz cone R_- = <t_1, t_2, q>.

A ring hom R_- -> M_k(F_2) is (Q, T1, T2) with Q^2 = Q, T1 Q = T1, T2 Q = 0 (the defining
relations of R_- = F_2<t_1,t_2,q | q^2 = q, t_1 q = t_1, t_2 q = 0>).  Up to conjugacy
Q = diag(1^r, 0^(k-r)); then T1 is supported on the first r columns, T2 on the last k-r.

For words w in {1,2}^N put t_w = t_{w_N} ... t_{w_1}.  The depth-N root code is
C_N = {S subset {1,2}^N : sum_{w in S} t_w = 0}.  We record, per shadow,
  d_N = minimum weight of a nonzero codeword (1: some t_w = 0; 2: a collision; 3: a
        three-term relation; otherwise the Singleton bound rank+1 is reported with '<=')
and the weight-depth cost W = min_N N * d_N (code bound: head <= d_N * max depth-N defect).
Only shadows with Q != 0 are counted (Q = 0 forces the head to vanish).

Usage: python3 root_code_census.py [kmax] [Nmax] [samples_for_k4]
"""
import itertools
import random
import sys


def mat_mul(a, b, k):
    # a, b: tuples of k row bitmasks (bit j = column j)
    out = []
    for i in range(k):
        row = 0
        ai = a[i]
        for j in range(k):
            if (ai >> j) & 1:
                row ^= b[j]
        out.append(row)
    return tuple(out)


def flatten(m, k):
    v = 0
    for i, row in enumerate(m):
        v |= row << (i * k)
    return v


def rank_f2(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def depth_profile(T1, T2, k, nmax):
    ident = tuple(1 << i for i in range(k))
    level = [ident]
    prof = []
    for n in range(1, nmax + 1):
        level = [mat_mul(T, w, k) for w in level for T in (T1, T2)]
        vecs = [flatten(m, k) for m in level]
        s = set()
        dup = False
        for v in vecs:
            if v in s:
                dup = True
            s.add(v)
        if 0 in s:
            prof.append((n, 1, ''))
            continue
        if dup:
            prof.append((n, 2, ''))
            continue
        three = any((a ^ b) in s for a, b in itertools.combinations(s, 2))
        if three:
            prof.append((n, 3, ''))
            continue
        r = rank_f2(vecs)
        if r < len(vecs):
            prof.append((n, r + 1, '<='))
        else:
            prof.append((n, None, ''))
    return prof


def shadows(k, r, sample=None):
    cols1 = [(1 << r) - 1] if r else [0]
    mask1 = (1 << r) - 1
    mask2 = ((1 << k) - 1) ^ mask1
    rows1 = [x for x in range(1 << k) if x & ~mask1 == 0]
    rows2 = [x for x in range(1 << k) if x & ~mask2 == 0]
    if sample is None:
        for t1 in itertools.product(rows1, repeat=k):
            for t2 in itertools.product(rows2, repeat=k):
                yield t1, t2
    else:
        for _ in range(sample):
            yield (tuple(random.choice(rows1) for _ in range(k)),
                   tuple(random.choice(rows2) for _ in range(k)))


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    samp = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    random.seed(20260917)
    for k in range(1, kmax + 1):
        for r in range(1, k + 1):
            worst = 0
            hist = {}
            first_depth_worst = 0
            count = 0
            smp = None if k <= 3 else samp
            for T1, T2 in shadows(k, r, smp):
                count += 1
                prof = depth_profile(T1, T2, k, nmax)
                costs = [n * d for (n, d, _) in prof if d is not None]
                W = min(costs) if costs else None
                first = min((n for (n, d, _) in prof if d is not None), default=None)
                hist[W] = hist.get(W, 0) + 1
                if W is not None:
                    worst = max(worst, W)
                if first is not None:
                    first_depth_worst = max(first_depth_worst, first)
            print(f"k={k} r={r} shadows={count}{' (sampled)' if smp else ''} "
                  f"max_W={worst} max_first_codeword_depth={first_depth_worst} hist_W={sorted(hist.items(), key=lambda t: (t[0] is None, t[0] or 0))}")


if __name__ == '__main__':
    main()
