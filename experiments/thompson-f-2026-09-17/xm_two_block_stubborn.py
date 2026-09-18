#!/usr/bin/env python3
"""Check the two-block stubborn sets for X_m = {x_0, ..., x_m}.

Claim `thompson-f-generator-sets-admit-no-private-pivot-order`:
for D >= m, N = D + m + 2 and a cut 1 <= c < N with c <= D + 1 and N - c <= D + 1,
Z(m, D, c) = {forests with D carets, all carets on leaves in [0, N), no caret containing both
leaves c-1 and c} is stubborn for X_m, and every z in Z has exactly one Z-private successor,
namely x_(r1-1) z where r1 is the number of roots of z inside [0, c).

Products are computed on forests directly (merge roots j and j+1), independently of the
normal-form insertion rule used by stubborn_core.cpp. For D = m the set is compared with the
core that stubborn_core.cpp computes from M_(m, 2m).

usage: xm_two_block_stubborn.py [path/to/stubborn_core binary]
"""
import itertools, math, subprocess, sys, tempfile, os
from collections import Counter

def forest_of(w, K):
    """Normal form i_1 <= ... <= i_D -> tuple of the first K roots; x_(i_D) is applied first."""
    roots = [((i,), i, i) for i in range(K)]  # (tree, lo leaf, hi leaf)
    carets = []
    for j in reversed(w):
        a, b = roots[j], roots[j + 1]
        node = ((a[0], b[0]), a[1], b[2])
        carets.append((a[1], b[2]))
        roots[j:j + 2] = [node]
    return tuple(r[0] for r in roots[:K - len(w)]), carets

def merge(f, j):
    return f[:j] + ((f[j], f[j + 1]),) + f[j + 2:]

def is_trivial(t):
    return len(t) == 1 and isinstance(t[0], int)

def leaves(t):
    return 1 if is_trivial(t) else leaves(t[0]) + leaves(t[1])

def block_set(D, c, N):
    K = 3 * N
    out = {}
    for w in itertools.combinations_with_replacement(range(N), D):
        f, carets = forest_of(w, K)
        if all(b < N and not (a < c <= b) for (a, b) in carets):
            out[w] = f
    assert len(set(out.values())) == len(out), "normal forms not injective on forests"
    return out

def f_count(n, carets):
    r = n - carets
    if r < 1 or r > n: return 0
    return r * math.comb(2 * n - r - 1, n - 1) // n

def check(m, D, c):
    N = D + m + 2
    Z = block_set(D, c, N)
    Zf = set(Z.values())
    assert len(Zf) > 0
    pred = Counter()
    for f in Zf:
        for j in range(m + 1):
            pred[merge(f, j)] += 1
    hist = Counter()
    for f in Zf:
        priv = [j for j in range(m + 1) if pred[merge(f, j)] == 1]
        hist[len(priv)] += 1
        # r1 = number of roots with leaves in [0, c)
        acc, r1 = 0, 0
        while acc < c:
            acc += leaves(f[r1]); r1 += 1
        assert acc == c, "caret crosses cut"
        assert priv == [r1 - 1], (m, D, c, f, priv, r1)
    assert set(hist) == {1}, hist
    return len(Zf)

def main():
    binary = sys.argv[1] if len(sys.argv) > 1 else None
    for m in range(1, 6):
        for D in range(m, m + 3):
            N = D + m + 2
            for c in range(1, N):
                if c <= D + 1 and N - c <= D + 1:
                    if math.comb(N + D - 1, D) > 300000: continue
                    n = check(m, D, c)
                    print(f"m={m} D={D} N={N} c={c} |Z|={n} every point has exactly 1 private successor", flush=True)
    for m in range(1, 7):
        n = m + 1
        formula = sum(f_count(n, a) * f_count(n, m - a) for a in range(0, m + 1))
        Z = block_set(m, m + 1, 2 * m + 2)
        assert len(Z) == formula
        line = f"m={m} D=m |Z_m|={len(Z)} formula={formula}"
        if binary:
            with tempfile.TemporaryDirectory() as td:
                cf = os.path.join(td, "core.txt")
                spec = ";".join(str(i) for i in range(m + 1))
                out = subprocess.run([binary, str(m), str(2 * m), spec, cf], capture_output=True, text=True).stdout
                core = {tuple(map(int, l.split(","))) for l in open(cf) if l.strip()}
                assert core == set(Z.keys()), (m, len(core), len(Z))
                line += f" core(M_(m,2m)) equal ({len(core)} points)"
        print(line, flush=True)
    print("OK")

if __name__ == "__main__":
    main()
