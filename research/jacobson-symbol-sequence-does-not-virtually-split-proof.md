---
rg: 2
id: jacobson-symbol-sequence-does-not-virtually-split-proof
kind: route
title: Compare the index of a commuting diagonal lift on the image layer of a lifted unipotent elementary matrix with its Toeplitz index on the first coordinate
target: jacobson-symbol-sequence-does-not-virtually-split
requires:
  - jacobson-symbol-sequence-does-not-split
---

Notation as in the target. All vector spaces are over `F_2`. From
`jacobson-symbol-sequence-does-not-split` (established) we use its Step 0 facts (F1) composition, (F2)
finite-rank perturbation and (F4) `ind S = -1`, `ind T = +1` for Fredholm maps, and its Step 1: every
`g~ in E` with symbol `g` equals any fixed `t(g) in M_n(J)` with symbol `g` plus a finite-rank operator on `V`.

## Step 0. Subspace-relative index

Subspaces `X, X'` of `V` are *commensurable* if `X cap X'` has finite codimension in both; put
`[X : X'] = dim X/(X cap X') - dim X'/(X cap X')`. Commensurability is an equivalence relation and
`[X:X''] = [X:X'] + [X':X'']` (compute all three against `X cap X' cap X''`, which has finite codimension in
each).

For a linear map `B` of `V` and a subspace `X`, call `(X, B)` *admissible* if `ker B cap X` is
finite-dimensional and `B X` is commensurable with `X`; then

```text
ind_X B = dim(ker B cap X) - [X : B X].
```

(I1) *Finite-codimension change.* Let `Z <= X` have finite codimension `d`. Then `(X,B)` is admissible iff
`(Z,B)` is, and then `ind_Z B = ind_X B`.
- `B Z <= B X` with `dim BX/BZ = d - (k_X - k_Z)`, where `k_Y = dim(ker B cap Y)`; and `k_X - k_Z <= d`.
- So `BZ` and `BX` are commensurable, and so are `Z` and `X`; admissibility transfers both ways.
- `[Z : BZ] = [Z:X] + [X:BX] + [BX:BZ] = -d + [X:BX] + d - k_X + k_Z`, hence
  `k_Z - [Z:BZ] = k_X - [X:BX]`.

(I2) *Commensurable change.* If `X, X'` are commensurable and `(X,B)` is admissible, then `(X',B)` is
admissible and `ind_(X') B = ind_X B`. Apply (I1) twice through `Y = X cap X'`.

(I3) *Finite-rank perturbation.* If `F` has finite rank and `(X,B)` is admissible, then `(X, B+F)` is
admissible and `ind_X (B+F) = ind_X B`. With `Z = X cap ker F` (finite codimension in `X`),
`B|_Z = (B+F)|_Z`; apply (I1) to `B` and then, upward, to `B+F`.

(I4) *Invariant subspaces.* If `B X <= X` and `B|_X : X -> X` is Fredholm, then `(X,B)` is admissible and
`ind_X B = ind(B|_X)`. In particular, if `B` is injective and `B X = X`, then `ind_X B = 0`.

(I5) *Images of perturbed maps.* If `t - t_0` has finite rank, then `tV` and `t_0 V` are commensurable:
with `K = ker(t - t_0)` of finite codimension, `tK = t_0 K` has codimension at most `dim V/K` in both.

## Step 1. The Toeplitz side

Fix `a != 0` in `A` and `k != 0`. Write `a = z^(-j) b` with `j >= 0` and `b in F_2[z]` nonzero, and put
`t(a) = T^j b(S) in J`, which has symbol `a`.
- `b(S)` is multiplication by `b` on `V_+ = F_2[z]` (via `e_m <-> z^m`): injective with cokernel of dimension
  `deg b`. So `t(a)` is Fredholm by (F1), and `im t(a)` has finite codimension in `V_+`.
- `t_0 := x_12(t(a)) + 1 = E_12 (x) t(a)` (in characteristic 2; the map sending the second coordinate into the first by
  `t(a)`, zero elsewhere) has symbol `u_a + 1`. Its image is `im t(a) (+) 0 (+) ... (+) 0`, which is
  commensurable with the first coordinate `X_1 = V_+ (+) 0 (+) ... (+) 0`.
- For `k > 0` put `t(h^k) = diag(S^k, S^k, T^(2k), 1, ..., 1)`; for `k < 0` put
  `t(h^k) = diag(T^(|k|), T^(|k|), S^(2|k|), 1, ..., 1)`. Its symbol is `h^k`.
- `t(h^k)` preserves `X_1` and restricts there to `S^k` (resp. `T^(|k|)`), of index `-k` by (F1), (F4).
  By (I4), `ind_(X_1) t(h^k) = -k`.

## Step 2. The lifted side

Suppose `u~, h~ in E` have symbols `u_a`, `h^k` and `u~ h~ = h~ u~`. Put `t = u~ + 1`. (No finite-order
condition on `u~` is needed.)
- `t h~ = h~ t`, so `h~(tV) = t(h~ V) = t V`, and `h~` is injective. By (I4), `ind_(tV) h~ = 0`.
- `t` has symbol `u_a + 1`, so `t - t_0` has finite rank (Step 1 of the prerequisite). By (I5), `tV` is
  commensurable with `t_0 V`, hence with `X_1`.
- By (I2), `ind_(X_1) h~ = ind_(tV) h~ = 0`.

## Step 3. Comparison

`h~ - t(h^k)` has finite rank (Step 1 of the prerequisite). By (I3) and Step 1,
`0 = ind_(X_1) h~ = ind_(X_1) t(h^k) = -k`, contradicting `k != 0`. This proves (NVS).

Commutation in `Q`: `h^k x_12(a) h^(-k) = x_12(z^k a z^(-k)) = x_12(a)`.

## Step 4. Corollary: no virtual section

Let `Gamma <= Q` have finite index `m` and suppose `s : Gamma -> E` is a section.
- `U_12 = {x_12(a) : a in A} ~= (A,+)` is infinite and `[U_12 : U_12 cap Gamma] <= m`, so `Gamma` contains
  some `u_a` with `a != 0`.
- Among the cosets `h^i Gamma`, `0 <= i <= m`, two coincide, so `h^k in Gamma` for some `1 <= k <= m`.
- Then `u~ = s(u_a)` and `h~ = s(h^k)` are commuting lifts. This contradicts (NVS).

For a subgroup containing `q (u_a, h^k) q^(-1)`, conjugate the putative section by any lift of `q`.

## Step 5. Sanity checks

- **One-sided halves.** Over `SL_n(F_2[z])` the analytic Toeplitz lifts are a section
  (`jacobson-one-sided-symbol-preimages-are-lef`). No element there has the form `h^k`, `k != 0`: every
  diagonal element of `SL_n(F_2[z])` is constant. Consistent.
- **Bilateral ambient.** In `H_bi` the shift is invertible and all indices vanish, matching the genuine
  semidirect structure there.
- **Finite dimensions.** In finite dimension every relative index vanishes, so this obstruction is invisible
  to matrix models; it constrains sections, not approximations.
- **What is used.** Only exact commutation `u~ h~ = h~ u~`, which makes `tV` exactly `h~`-invariant, and the
  fact that the symbol `u_a + 1 = a E_12` has image of rank one over `A` inside the first coordinate, where
  the diagonal entry of `h^k` is `z^k` with `k != 0`. The same proof works for `x_ij(a)` and any diagonal
  `d in Q` with `d_i = d_j = z^k`, `k != 0`.
