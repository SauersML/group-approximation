---
rg: 2
id: weak-determinant-violations-move-to-cubic-operators-proof
kind: route
title: Realize each monomial as a tree path, trade signs for an identity block, and pad row and column deficits with a central gadget whose adjugate corner vanishes
target: weak-determinant-violations-move-to-cubic-operators
requires: []
artifacts:
  - experiments/determinant-cubic-linearization-2026-09-17/linearize_check.py
  - experiments/determinant-cubic-linearization-2026-09-17/output.txt
  - experiments/determinant-cubic-linearization-2026-09-17/gadget_search.py
  - experiments/determinant-cubic-linearization-2026-09-17/gadget_output.txt
---

**Inputs.** The proof uses:
- Lück, *L2-invariants*, Theorem 3.14:
  - `det` is multiplicative on weak isomorphisms;
  - the determinant of a block-triangular matrix with weak-isomorphism
    diagonal blocks is the product of the blocks' determinants;
  - an invertible matrix `U` with `U - I` nilpotent, or unitary, has
    `det U = 1`.
- Square matrices over a finite von Neumann algebra: injective iff weak
  isomorphism.
- Induction: `det` over a subgroup equals `det` over the overgroup.
- For `f in C[Z]`, `det_{N(Z)} f` is the Mahler measure `m(f)`.
- Theorem 5 of `determinant-norm-room-2026-09-16` (the artifact behind
  `cubic-serre-violations-transfer-to-norm-near-3-over-sqrt2`).

## 1. Schur trees

Let `T in M_n(Z[G])` be injective. Then no row or column of `T` is zero.
Write `T = sum_t eps_t g_t e_(i_t k_t)` as a list of signed monomials, with
`eps_t = +-1` and repetitions allowed.
- For each row `i`, build a binary out-tree whose leaves are the monomials with
  `i_t = i`.
- For each column `k`, build a binary in-tree whose leaves are the monomials
  with `k_t = k`.

A single leaf is its own root.

Index `L` by `[n]` together with the tree nodes. Its nonzero entries are
coefficient-`1` monomials:
- `L(i, root of out-tree i) = 1`: the block `E`.
- `L(v, child) = 1` for each out-tree node `v` and each of its children.
- `L(child, v) = 1` for each in-tree node `v` and each of its children.
- `L(root of in-tree k, k) = 1`: the block `F`.
- `L(out-leaf of t, in-leaf of t) = eps_t g_t`: the bridges.
- `L(v, v) = -1` for every tree node `v`.

So `L = [[0, E], [F, -I + K]]`, where `K` holds the tree and bridge entries.

**`K` is nilpotent.** Every `K`-path runs down an out-tree, across one bridge
and up an in-tree, so its length is bounded.

**The Schur complement is `T`.** It equals
`-E(-I+K)^(-1) F = E (sum_p K^p) F`. Its `(i,k)` entry sums the products along
paths from out-root `i` to in-root `k`. Each such path crosses exactly one
bridge `t` with `(i_t, k_t) = (i,k)`, and every other factor is `1`. So the
complement is `T`.

**Determinant.** Write `D = -I + K`. Then

```text
L = [[I, E D^(-1)], [0, I]] . [[T, 0], [0, D]] . [[I, 0], [D^(-1) F, I]].
```

The outer factors are unipotent, so each has determinant `1`. `D` is invertible
with `det D = det(-I) det(I-K) = 1`. Hence `L` is injective and `det L = det T`.

## 2. Sign removal

Split `L = P - N`. Here `P` holds the `+1`-coefficient entries and `N` the
negated `-1`-coefficient entries: the tree diagonal and the negative bridges.
Set `M1 = [[P, N], [I, I]]`. Then

```text
M1 = [[L, N], [0, I]] . [[I, 0], [I, I]].
```

The second factor is unipotent. The first is block upper triangular with
injective diagonal blocks. So `M1` is injective and `det M1 = det L`.

Every entry of `M1` is `0` or a single group element with coefficient `1`.

**Row sums.** Rows of `M1` restricted to the first block count the entries
of `L`:

| row | sum |
|---|---|
| `[n]` | 1 |
| internal out-node | 2 children + diagonal = 3 |
| out-leaf | bridge + diagonal = 2 |
| in-node | parent (or `F`) + diagonal = 2 |
| bottom rows | 2 |

**Column sums.**
- Columns in the `P`-block: the `P`-column has at most `2` entries (at most
  `2` in-tree children, or one parent or `E` or `F` entry plus possibly a
  positive bridge on an in-leaf), plus `1` from the bottom `I`.
- Columns in the `N`-block: the diagonal `-1` plus possibly a negative bridge
  on an in-leaf, plus `1` from the bottom `I`.

All row and column sums are at most `3`.

## 3. Padding with a central gadget

Let `d_R(r) = 3 - (row sum r)` and `d_C(c) = 3 - (column sum c)`. They are
nonnegative with `|d_R| = |d_C| = g`, since both count `3N1 - (total)`, where
`N1` is the size of `M1`. List the row-deficit units `a_1..a_g` and the
column-deficit units `b_1..b_g`.

Put `G(s) = [[0,1,s],[1,1,1],[s,1,1]]` over `Z[Z]`, with `s` central in `K`. Then:
- `det G = -(1-s) + s(1-s) = -(1-s)^2 =: Phi`;
- `adj(G)_(00) = det[[1,1],[1,1]] = 0`;
- row `0` and column `0` have coefficient sum `2`, and the others have `3`.

Take `G_all = diag(G, ..., G)` with `g` copies. Define:
- `E'(a_j, column 0 of copy j) = 1`;
- `F'(row 0 of copy j, b_j) = 1`;
- `M' = [[M1, E'], [F', G_all]]`.

Then every row and column of `M'` has coefficient sum exactly `3`.

**Determinant.** Let `A = diag(adj G, ..., adj G)`. Then `A G_all = Phi I`,
and `Phi` is central. We have

```text
[[Phi I, -E' A], [0, I]] . M' = [[Phi M1 - E' A F', Phi E' - E' A G_all], [F', G_all]]
                              = [[Phi M1, 0], [F', G_all]].
```

- `E' A F' = 0`: its `(a_j, b_j')` entry is nonzero only when `j = j'`, and
  then it equals `adj(G)_(00) = 0`.
- `Phi E' - E' A G_all = Phi E' - E' Phi = 0`.

Now `Phi` is a nonzero element of `C[Z]`, so it is injective, with
`det_{N(K)} Phi = m(-(1-s)^2) = 1`. Likewise `det G = 1` with `G` injective.
The right-hand side is block lower triangular with injective diagonal blocks,
so its determinant is `det(Phi I)^(N1) det M1 det(G)^g = det M1`. The left
factor is block upper triangular with determinant `1`.

Therefore `M'` is injective and `det M' = det M1 = det T`.

## 4. Monomial form and the bipartite double

**König.** `M'` is the biadjacency matrix of a 3-regular bipartite multigraph
whose edges are labelled by elements of `K`. König's theorem splits it into
three perfect matchings, so `M' = u1 + u2 + u3` with monomial unitaries.
Hence `det(1 + w1 + w2) = det(u1^* M') = det M'`, with `w_i = u1^* u_(i+1)`.

Conversely, an injective `1 + w1 + w2` is itself a nonnegative matrix with row
and column sums `3`.

**Bipartite double.** `B = [[0, M'], [M'^*, 0]]` has the following properties:
- it is self-adjoint with coefficients in `N[K]`;
- its row sums are the row and column sums of `M'`, hence all `3`;
- its diagonal is zero, so it has no inversions;
- `|B| = diag(|M'^*|, |M'|)`, so `B` is injective and `det B = (det M')^2`.

**Corollary 1, all groups.**
- `DC_wi` for all groups implies `det(1 + w1 + w2) >= 1` for injective
  operators of that form, and that implies the cubic statement: a cubic
  injective `B` is a nonnegative square matrix with row and column sums `3`,
  so by König `det B = det(1 + w1 + w2)` for monomial `w_i`.
- Conversely, suppose some injective `T` over `G` has `det T < 1`. View `T`
  over `G x Z`, where the determinant is unchanged. Theorem 1 then gives a
  cubic injective `B` with `det B < 1`, and an injective `1 + w1 + w2` with
  `det < 1`.

## 5. Theorem 2: dropping `||r_B|| < 3`

Let `B` in `M_k(Z[H])` be cubic without inversions, and suppose
`integral_{R != 0} log|R| d mu_B = -delta < 0`. Take `R_m = (t^2-9) R^m` and
`Q_m = R_m o p_L`. The spectral transfer identity, artifact Theorem 5(3),
does not use the norm hypothesis:

```text
integral_{Q_m != 0} log|Q_m| d mu_(A_L)
  = (k/2) sum_(j : R_m(3(-1)^j) != 0) log|R_m(3(-1)^j)| + L integral_{R_m != 0} log|R_m| d mu_B.
```

- The Dirichlet sum is empty, because `R_m(+-3) = 0`.
- `supp mu_B` lies in `[-3,3]` and has total mass `k`. So
  `integral_{R_m != 0} log|t^2-9| d mu_B <= k log 9`. This integral may be
  `-infinity`, which only helps.
- `{R_m != 0} = {R != 0} \ {+-3}`. The values `R(+-3)` are integers. When one
  is nonzero, `log|R(+-3)| >= 0`. So removing the atoms at `+-3` can only
  decrease the integral:
  `integral_{R_m != 0} log|R| d mu_B <= -delta`.

Hence the right-hand side is at most `L(k log 9 - m delta)`, which is `< 0`
for `m > k log 9 / delta`. The norm of `A_L` is bounded by artifact Theorem 5(1)
independently of `B`.

**Corollary 3, norm band.**
- Serre below `3/sqrt 2 + eps` over every group implies CubicSerre over every
  group.
- Taking `Q = t`, CubicSerre implies `det B >= 1` for injective cubic `B`.
- By Corollary 1, that gives `DC_wi` for every group.

## 6. The per-group chain

1. **`DC(H) => DC(H x Z)`.** This is Schick's amenable-extension theorem
   (Lück, Theorem 13.3). A direct argument:
   - `H x Z/q` contains `H` with finite index, so it satisfies DC.
   - For `A` over `H x Z`, let `A_q` be the image over `H x Z/q`. The `p`-th
     moment of `A_q^* A_q` equals that of `A^* A` once `q` exceeds `p` times
     the `Z`-degree span of `A^* A`, so every moment converges. The norms are
     uniformly bounded, so the spectral measures converge weakly.
   - `f = 1_(lambda > 0) log lambda` is upper semicontinuous and bounded above
     on the common support, with `f(0) = 0`. So
     `2 log det' A = integral f d mu >= limsup integral f d mu_q >= 0`.
2. **`DC => NR`.** This follows from `determinant-conjecture-iff-serre-class-spectra`.
3. **`NR => CubicSerre`.** This is Section 5.
4. **`CubicSerre => CubicDet`.** Take `Q = t`.
5. **`CubicDet(H x Z) => DC_wi(H x Z)`.** This is Theorem 1 applied to
   `G = H x Z`, which produces a cubic operator over `H x Z x Z`. To stay at
   `H x Z`, run the padding with the `Z` coordinate `s` of `H x Z` itself: the
   gadget needs only a central element of infinite order, and `T` may already
   involve `s`.
6. **`DC_wi(H x Z) => DC_wi(H)`.** This is induction.

## 7. Obstructions

**No scalar gadget.** Pad instead with `M'' = [[M1, E'], [F', G]]`, where
`E'`, `F'` and `G` are nonnegative integer matrices, every row and column of
`M''` has sum `3`, and `|det G| = 1`. The Schur complement is
`M1 - E' G^(-1) F'`; exactness of the padding asks for the cross term
`E' G^(-1) F'` to vanish. It cannot, if some row of `M1` has a deficit:
- The rows of `G` have sums `G1 = 3*1 - d_R`, where `d_R = F' 1`.
- `u = G^(-1) 1` is integral, because `|det G| = 1`. Hence
  `G^(-1) d_R = G^(-1)(3*1 - G1) = 3u - 1`.
- So `E' G^(-1) F' 1 = E'(3u - 1) = 3E'u - E'1`.
- `E'1` is the row-deficit vector of `M1`, with entries in `{0,1,2}`. On a
  row with deficit `1` or `2`, the entry of `3E'u - E'1` is nonzero mod `3`.

So `E' G^(-1) F' != 0`. `gadget_search.py` checks the entrywise form by
exhaustive search for sizes up to `4`: no `G` with `|det G| = 1` and the
margins above has `(G^(-1))_(c r) = 0` for all `c in supp d_C` and
`r in supp d_R`.

**Finite groups.** For finite `H` and cubic `M'` over `H`, the integer matrix
`rho_reg(M')` has all row sums `3`, so `1` is an eigenvector with eigenvalue
`3` and `3 | det rho(M')`. So `det_H M' in {0} U [3^(1/|H|), infinity)`, and no
cubic model over `H` can have determinant `1`. Any exact cubic linearization
must change the group.

## 8. Kernel gap (open)

With a kernel, `det'` is not multiplicative under unipotent factors. The
`2 x 2` example is `[[1,0],[1,1]] . [[1,0],[0,0]]`, with `det' = sqrt 2`.
Section 1 therefore does not transfer `det'`. `output.txt` records the
`T = 1 + h` control, where `det'` of `T`, `L` and `M1` all differ. Upgrading
Theorem 1 to `DC_wi => DC` needs a kernel-aware linearization, and it remains
open.
