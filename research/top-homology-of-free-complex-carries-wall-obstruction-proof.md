---
rg: 2
id: top-homology-of-free-complex-carries-wall-obstruction-proof
kind: route
title: Dimension shifting splits off the top cycles as a projective summand whose class is the Euler class
target: top-homology-of-free-complex-carries-wall-obstruction
requires:
  - fp-type-fp-group-is-type-f-iff-wall-class-vanishes
---

Let `C_* = C_*(X)` be the cellular chain complex. The action is free and
cocompact, so each `C_k` is a finitely generated free `ZG`-module. Augment by
`C_0 → Z → 0`. `X` is connected and `H_k(X) = 0` for `1 ≤ k ≤ N − 1`, so

`C_N → C_{N−1} → ⋯ → C_0 → Z → 0`

is exact everywhere except at `C_N`, where the kernel of `∂_N` is
`Z_N = H_N(X)` (there are no `(N+1)`-cells).

**Projectivity.** For `j ≥ 1` let `K_j = ker(C_{j−1} → C_{j−2})`, with
`C_{−1} = Z`. Dimension shifting gives
`Ext^i_{ZG}(K_j, M) ≅ H^{i+j}(G; M)` for `i ≥ 1`, and these vanish when
`j ≥ d`, since `cd G = d`. So `K_j` is projective for `j ≥ d`. By exactness,
`K_N = im ∂_N`, so `0 → Z_N → C_N → K_N → 0` is exact. `K_N` is projective
because `N ≥ d`, so the sequence splits, and `Z_N` is a direct summand of the
finitely generated free module `C_N`: a finitely generated projective module.

**Euler class.** `0 → Z_N → C_N → ⋯ → C_0 → Z → 0` is a finite projective
resolution, so
`σ(G) = Σ_{i=0}^{N} (−1)^i [C_i] + (−1)^{N+1} [Z_N]`. The `[C_i]` are free and
vanish in `K̃_0(ZG)`, which leaves `σ(G) = (−1)^{N+1} [Z_N]`.

**Consequences.** If `σ(G) ≠ 0` then `[Z_N] ≠ 0` in `K̃_0(ZG)`, so `Z_N` is not
stably free. If instead `Z_N` is stably free then `σ(G) = 0`. For `G` finitely
presented, `fp-type-fp-group-is-type-f-iff-wall-class-vanishes` then gives type F.
Directly: with `Z_N ⊕ F ≅ F'` for finitely generated free `F, F'`, replace `C_N`
by `C_N ⊕ F` and map `F` to zero. The new kernel is `Z_N ⊕ F ≅ F'`, which gives a
finite free resolution. For a Rips complex `R_r(G,S)` of a torsion-free group,
freeness and cocompactness are steps 1–2 of
`contractible-rips-complex-gives-finite-classifying-space-proof`, which do not
use contractibility.
