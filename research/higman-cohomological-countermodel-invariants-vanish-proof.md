---
rg: 2
id: higman-cohomological-countermodel-invariants-vanish-proof
kind: route
title: The cellular boundary of a Higman cycle is (1-m) times a cyclic permutation, so H_2 of the presentation complex vanishes and every trivial-coefficient obstruction group is zero
target: higman-cohomological-countermodel-invariants-vanish
requires:
  - dadarlat-matricial-stability-obstruction
artifacts:
  - research/artifacts/higman-acyclic-cohomology-kill-2026-09-17.md
---

Indices are in `Z/k`.  Write `Gamma = H_k(m)` and `X = X_k(m)`.

## Step 1: the cellular chain complex

`X` has one 0-cell, 1-cells `e_i` (one per generator), and 2-cells `f_i`
attached along `r_i = g_i g_(i+1) g_i^(-1) g_(i+1)^(-m)`.  The cellular chain
complex is

```text
0 -> Z^k --d_2--> Z^k --d_1=0--> Z -> 0.
```

`d_2 f_i` is the abelianized exponent sum of `r_i`:

```text
d_2 f_i = e_i + e_(i+1) - e_i - m e_(i+1) = (1-m) e_(i+1).
```

So `d_2 = (1-m) C`, where `C` is the cyclic permutation matrix, and
`det d_2 = +-(m-1)^k`, which is nonzero because `m >= 2`.

- `H_2(X;Z) = ker d_2 = 0`.
- `H_1(X;Z) = coker d_2 = (Z/(m-1))^k`.  This equals `H_1(Gamma;Z)`, since
  `H_1` depends only on `pi_1`.
- `H^2(X;Z) = coker d_2^T = (Z/(m-1))^k`.

For `m = 2`, `d_2 = -C` is unimodular, so `H_1 = H^2(X;Z) = 0`.

## Step 2: Hopf's theorem

For any connected CW complex `X` with `pi_1 X = Gamma`, Hopf's exact sequence
`pi_2 X -> H_2(X;Z) -> H_2(Gamma;Z) -> 0` holds.  Equivalently, `BGamma` is
obtained from `X` by attaching cells of dimension at least 3, which adds no
2-cycles, so `H_2(X) -> H_2(BGamma)` is surjective.  Hence
`H_2(Gamma;Z) = 0`.  This uses no asphericity.

## Step 3: the trivial-coefficient obstruction groups

Group cohomology with trivial coefficients is the cohomology of
`Hom_Z(F_*, V)`, where `F_* = Z tensor_(ZGamma) P_*` and `P_*` is a free
resolution.  `F_*` is a complex of free abelian groups whose homology is
`H_*(Gamma;Z)`, so the universal coefficient theorem gives

```text
H^2(Gamma;V) = Hom(H_2(Gamma;Z),V) (+) Ext^1_Z(H_1(Gamma;Z),V).
```

- The first summand is zero by Step 2.
- If `V` is a real or complex vector space, `V` is divisible, hence injective
  as an abelian group, and `Ext^1_Z(-,V) = 0`.

So `H^2(Gamma;V) = 0`.  Now:

- `Q(R) = c_0(N,R)/c_00(N,R)` and `Q(C)` are vector spaces, so the
  Dadarlat--Glebe class `[rho]` lies in the zero group.
- Their Theorems 1.1, 1.2(1), 1.4 and Corollary 1.3 all assume a nonzero
  class in `H^2(Gamma,R)`, and `H^2(Gamma;R) = 0`.  Theorem 1.2(2) needs a
  nonzero comparison map into `H^2(Gamma,R) = 0`.
- The Exel--Loring formula (Theorem 1.1 of arXiv:2111.05755, recorded in
  `exel-loring-mark-quantization`) attaches an integer to each
  `x in H_2(Gamma;Z)`.  Only `x = 0` exists, and its invariant is `0`.

This proves item 1 and item 2 of the target for all `k >= 1`, `m >= 2`.

## Step 4: Higman's group

Theorem 8 and Corollary 9 of Leary--Saadetoglu, quoted verbatim in the
artifact and attributed there to Higman and Baumslag--Dyer--Heller, say that
`Hig` is torsion-free, that `X_4(2)` is a classifying space, and that `Hig`
is acyclic.

- **Dadarlat's Theorem 1.1.**  Its hypothesis is `H^(2k)(G,Q) != 0` for some
  `k >= 1`, as quoted in `dadarlat-matricial-stability-obstruction`.  Since
  `BHig = X_4(2)` is 2-dimensional, `H^j = 0` for `j >= 3`, and
  `H^2(Hig;Q) = 0` by Step 3.  The hypothesis fails in every degree, so the
  theorem yields nothing for `Hig`.
- **Delocalized sectors.**  The sectors of the delocalized Chern character
  are indexed by conjugacy classes of finite-order elements.  Torsion-free
  means only `(1)` exists, and its sector `H^*(Hig;Q)` vanishes in positive
  degrees.
- **Almost-flat K-theory.**  For a 2-dimensional CW complex the
  Atiyah--Hirzebruch spectral sequences degenerate (`d_3` leaves the range).
  So `K^0(X) = H^0 (+) H^2 = Z (+) 0`, `K^1(X) = H^1 = 0`, and
  `K_0(X) = H_0 (+) H_2 = Z`, with no extension problem, since `H^2` and
  `H_2` are zero.  An almost-flat bundle `E` on `X` therefore has
  `[E] = rank(E)[1]`.  Every pairing against `K_0(X)` is `rank` times its
  value on the point, which is the value for the trivial representation.

This proves item 3.  The "Obstruction" and "What survives" paragraphs of the
target only restate which invariants these groups carry, and add nothing
beyond Steps 1--4.
