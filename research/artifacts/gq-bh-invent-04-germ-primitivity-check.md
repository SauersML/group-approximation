# Germ-primitivity check for Busemann transplant minimality (bh-invent-04, 2026-09-18)

This is the computation behind `cmsz-lattices-carry-free-minimal-quantum-rigid-sfts`, item (GP).
- **Job.** One Slurm job, 1328369, partition msismall (node acl14), 1 core, 1 GB, 6 s, exit 0. Python 3.6.8,
  standard library only. The scratch directory was deleted afterwards.
- **Inputs.** Two cyclic triangle presentations over the Fano plane (`q = 2`), with `λ(x) = x + {1,2,4}` mod 7
  and `T = {(x, x+d_1, x+d_1+d_2)}`. Here `(d_1, d_2, d_3)` runs over the rotations of `(1,2,4)`, or of
  `(1,4,2)`. The CMSZ axioms (A)–(C) and the projective-plane axioms are checked in the script.
- **Tiles.** Flat unit cells of a sector, with labels `(x, s, y, x', y')`: bottom, diagonal, left, top,
  right. They satisfy `(x,s,y) ∈ T`, `(s,x',y') ∈ T` and `x' ≠ y`.
- **Adjacencies.** These are the local flatness conditions of the hexagon at interior vertices and of the
  angle-π paths at wall vertices. They reduce to:
  - horizontal `H(A,B)`: `y'_A = y_B`, `x_B ≠ s_A`, `x'_A ≠ s_B`;
  - vertical `V(C,D)`: `x'_C = x_D`, `s_D ≠ y'_C`, `y_D ≠ s_C`.
- **Calibration.** The `F_2 × F_2` quadrant tiles `(x, y)` with non-backtracking moves, where minimality is
  proved (`busemann-transplant-minimality-is-horospherical-minimality`, item 5).

## Output (verbatim)

```text
host=acl14 py=/usr/bin/python3
python 3.6.8
[F2xF2 calibration] tiles=16 rowsums M1=[3] M2=[3] colsums M1=[3] M2=[3]
[F2xF2 calibration] M1M2==M2M1: True; max entry of M1M2: 1
[F2xF2 calibration] strongly connected (M1+M2): True; M1 alone: False; M2 alone: False
[F2xF2 calibration] positive M1^p1 M2^p2 (p1,p2<= 12): count=121 first=(2, 2) diagonal=(2, 2) congruent_mod3=(2, 2)
[A2 cyclic (1, 2, 4)] |T|=21 projective plane ok=True axioms A=True B=True C=True
[A2 cyclic (1, 2, 4)] tiles=42 rowsums M1=[4] M2=[4] colsums M1=[4] M2=[4]
[A2 cyclic (1, 2, 4)] M1M2==M2M1: True; max entry of M1M2: 1
[A2 cyclic (1, 2, 4)] strongly connected (M1+M2): True; M1 alone: True; M2 alone: True
[A2 cyclic (1, 2, 4)] positive M1^p1 M2^p2 (p1,p2<= 12): count=141 first=(1, 3) diagonal=(2, 2) congruent_mod3=(2, 2)
[A2 cyclic (1, 4, 2)] |T|=21 projective plane ok=True axioms A=True B=True C=True
[A2 cyclic (1, 4, 2)] tiles=42 rowsums M1=[4] M2=[4] colsums M1=[4] M2=[4]
[A2 cyclic (1, 4, 2)] M1M2==M2M1: True; max entry of M1M2: 1
[A2 cyclic (1, 4, 2)] strongly connected (M1+M2): True; M1 alone: True; M2 alone: True
[A2 cyclic (1, 4, 2)] positive M1^p1 M2^p2 (p1,p2<= 12): count=141 first=(1, 3) diagonal=(2, 2) congruent_mod3=(2, 2)
DONE
rc=0

```

## Reading

- **Calibration.** It passes, and it is primitive at `(2,2)`, as predicted by hand.
- **Structure.** Row and column sums are `q^2 = 4`, and `M_1 M_2 = M_2 M_1` with 0/1 entries. So every 2×2
  block completes uniquely, and rectangles of tiles are the paths of a 2-graph. This agrees with
  Robertson–Steger's tile 2-graph: 42 = (q²+q+1)(q+1)q tiles, and row sums `q²`.
- **Primitivity.** `M_1^(p_1) M_2^(p_2) > 0` already at `(1,3)` and at `(2,2)`. Since row sums are positive,
  every larger degree works too. This includes the degrees `p_1 ≡ p_2 (mod 3)` needed by the type-preserving
  index-3 subgroup.
- **Consistency.** This agrees with `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`, item 2
  (`θ ≠ 0`), and with `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`.

## Script (as run)

```python
#!/usr/bin/env python3
# Germ-primitivity (GP) check for Busemann transplant minimality (bh-invent-04).
# 1. Calibration: F_2 x F_2 quadrant tiles, where minimality is proved (expect primitive at (2,2)).
# 2. Two cyclic triangle presentations over the Fano plane (q = 2), CMSZ axioms (A)-(C) checked;
#    tiles = flat unit cells (x, s, y, x2, y2) of a sector; H/V = horizontal/vertical flat adjacency.
#    Structural calibrations: row sums q^2, M1 M2 = M2 M1 with 0/1 entries (unique 2x2 completion).
#    GP <= some M1^p1 M2^p2 > 0 with p1, p2 >= 1 (type-preserving subgroup: p1 = p2 mod 3).
import sys

def matmul(A, B):
    n = len(A)
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(A[i], Bt[j])) for j in range(n)] for i in range(n)]

def boolify(A):
    return [[1 if v else 0 for v in row] for row in A]

def bpow(A, p):
    n = len(A)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for _ in range(p):
        R = boolify(matmul(R, A))
    return R

def positive(A):
    return all(v > 0 for row in A for v in row)

def strongly_connected(adj):
    n = len(adj)
    def reach(src, rev):
        seen = {src}; stack = [src]
        while stack:
            u = stack.pop()
            for v in range(n):
                e = adj[v][u] if rev else adj[u][v]
                if e and v not in seen:
                    seen.add(v); stack.append(v)
        return seen
    return len(reach(0, False)) == n and len(reach(0, True)) == n

def analyse(name, tiles, H, V, mod3=False, grid=12):
    n = len(tiles)
    M1 = [[1 if H(a, b) else 0 for b in tiles] for a in tiles]
    M2 = [[1 if V(a, b) else 0 for b in tiles] for a in tiles]
    r1 = sorted(set(map(sum, M1))); r2 = sorted(set(map(sum, M2)))
    c1 = sorted(set(map(sum, zip(*M1)))); c2 = sorted(set(map(sum, zip(*M2))))
    P12 = matmul(M1, M2); P21 = matmul(M2, M1)
    comm = P12 == P21
    maxent = max(max(row) for row in P12)
    both = [[M1[i][j] | M2[i][j] for j in range(n)] for i in range(n)]
    print(f"[{name}] tiles={n} rowsums M1={r1} M2={r2} colsums M1={c1} M2={c2}")
    print(f"[{name}] M1M2==M2M1: {comm}; max entry of M1M2: {maxent}")
    print(f"[{name}] strongly connected (M1+M2): {strongly_connected(both)}; M1 alone: {strongly_connected(M1)}; M2 alone: {strongly_connected(M2)}")
    B1 = boolify(M1); B2 = boolify(M2)
    pw1 = [None]; pw2 = [None]
    for p in range(1, grid + 1):
        pw1.append(bpow(B1, p)); pw2.append(bpow(B2, p))
    first = None; diag = None; pos_pairs = []
    for p1 in range(1, grid + 1):
        for p2 in range(1, grid + 1):
            if positive(boolify(matmul(pw1[p1], pw2[p2]))):
                pos_pairs.append((p1, p2))
    if pos_pairs:
        first = min(pos_pairs, key=lambda t: (t[0] + t[1], t))
        diag = min((p for p in pos_pairs if p[0] == p[1]), default=None)
        cong = min((p for p in pos_pairs if (p[0] - p[1]) % 3 == 0), key=lambda t: (t[0] + t[1], t), default=None)
    else:
        cong = None
    print(f"[{name}] positive M1^p1 M2^p2 (p1,p2<= {grid}): count={len(pos_pairs)} first={first} diagonal={diag} congruent_mod3={cong}")
    # minimal row-degree per level (sanity for extension counts)
    return comm and maxent <= 1, first, diag

def free_product_calibration():
    S1 = ['a', 'A', 'b', 'B']; S2 = ['c', 'C', 'd', 'D']
    inv = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'c': 'C', 'C': 'c', 'd': 'D', 'D': 'd'}
    tiles = [(x, y) for x in S1 for y in S2]
    H = lambda s, t: t[1] == s[1] and t[0] != inv[s[0]]
    V = lambda s, t: t[0] == s[0] and t[1] != inv[s[1]]
    return analyse("F2xF2 calibration", tiles, H, V)

def fano():
    P = list(range(7))
    lam = {x: frozenset((x + d) % 7 for d in (1, 2, 4)) for x in P}
    lines = set(lam.values())
    ok = len(lines) == 7
    for x in P:
        for y in P:
            if x < y:
                ok &= sum(1 for L in lines if x in L and y in L) == 1
    for L in lines:
        for M in lines:
            if L != M:
                ok &= len(L & M) == 1
    return P, lam, ok

def cyclic_T(order):
    nxt = {order[0]: order[1], order[1]: order[2], order[2]: order[0]}
    T = set()
    for x in range(7):
        for d1 in (1, 2, 4):
            y = (x + d1) % 7; z = (y + nxt[d1]) % 7
            T.add((x, y, z))
    return T

def check_T(T, P, lam):
    A = all(any((x, y, z) in T for z in P) == (y in lam[x]) for x in P for y in P)
    B = all((y, z, x) in T for (x, y, z) in T)
    C = all(sum((x, y, z) in T for z in P) <= 1 for x in P for y in P)
    return A, B, C

def a2_check(order):
    P, lam, plane_ok = fano()
    T = cyclic_T(order)
    A, B, C = check_T(T, P, lam)
    name = f"A2 cyclic {order}"
    print(f"[{name}] |T|={len(T)} projective plane ok={plane_ok} axioms A={A} B={B} C={C}")
    if not (plane_ok and A and B and C):
        print(f"[{name}] NOT a triangle presentation; skipped"); return None
    tiles = [(x, s, y, x2, y2) for (x, s, y) in sorted(T) for (s1, x2, y2) in sorted(T) if s1 == s and x2 != y]
    # tile fields: 0 bottom x, 1 diagonal s, 2 left y, 3 top x2, 4 right y2
    H = lambda A_, B_: A_[4] == B_[2] and B_[0] != A_[1] and A_[3] != B_[1]
    V = lambda C_, D_: C_[3] == D_[0] and D_[1] != C_[4] and D_[2] != C_[1] and D_[0] != C_[2]
    return analyse(name, tiles, H, V)

if __name__ == "__main__":
    print("python", sys.version.split()[0])
    free_product_calibration()
    for order in ((1, 2, 4), (1, 4, 2)):
        a2_check(order)
    print("DONE")
```
