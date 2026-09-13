---
rg: 2
id: sl3z-non-zariski-dense-fg-subgroups-are-fp-proof
kind: route
title: Proper Zariski closures in SL_3 have coherent integral points
target: sl3z-non-zariski-dense-fg-subgroups-are-fp
requires: []
---

**Tools.**

- (i) P. Hall: an extension of a finitely presented group by a finitely
  presented group is finitely presented.
- (ii) Finite presentability passes to finite-index subgroups and to
  finite-index overgroups.
- (iii) Finitely generated subgroups of virtually free groups are finitely
  presented; finitely generated discrete subgroups of `PSL_2(R)` (finitely
  generated Fuchsian groups) are finitely presented; finitely generated abelian
  groups are finitely presented.

Let `Zc` be the Zariski closure of `H`, `Zc°` its identity component, and
`H_1 = H ∩ Zc°`. Then `H_1` has finite index in `H`, is finitely generated,
and its Zariski closure is `Zc°`. So the complex linear span of `H_1` in
`M_3(C)` equals that of `Zc°`, since linear subspaces are Zariski closed. By
(ii) it suffices to show `H_1` is finitely presented.

**Case 1: `Zc°` acts irreducibly on `C^3`.**

- `Zc°` is reductive. Its unipotent radical `U` has a nonzero fixed subspace
  (Lie–Kolchin), which `Zc°` preserves because `U` is normal, so `U = 1`.
- Its centre acts by scalars (Schur), so the centre is finite and `Zc°` is
  semisimple.
- The semisimple Lie subalgebras of `sl_3(C)` are `0`, `sl_3` and copies of
  `sl_2`. A rank-two semisimple algebra other than `sl_3` has no faithful
  three-dimensional representation.
- `sl_2` acts irreducibly on `C^3` only through `Sym^2`. So `Zc° = SO(q)` for
  a nondegenerate quadratic form `q`, unique up to scalars. That line of forms
  is Galois stable, so `q` may be taken rational.

Then `H_1 <= SO(q)(R) ∩ SL_3(Z)` is a discrete subgroup of `SO(q)(R)`. If `q`
is definite, `SO(q)(R)` is compact and `H_1` is finite. Otherwise
`SO(q)(R) = SO(2,1)`, whose identity component is `PSL_2(R)`. In that case
`H_1 ∩ SO(q)(R)°` has index at most 2 in `H_1` and is a finitely generated
discrete subgroup of `PSL_2(R)`, hence finitely presented by (iii).

**Case 2: `Zc°` acts reducibly.** Then `C[H_1] != M_3(C)`, so `Q^3` is not an
absolutely irreducible `Q[H_1]`-module.

- **(2b) `Q^3` irreducible over `Q`.** The commutant `D` is a division algebra
  with `dim_Q D` dividing 3.
  - If `D = Q`, the double centralizer theorem gives `Q[H_1] = M_3(Q)`, which
    contradicts absolute reducibility.
  - So `dim_Q D = 3`. A central division algebra has square dimension over its
    centre, so `D` is a cubic field `K`.
  - `Q^3` is then a one-dimensional `K`-space and `Q[H_1] <= End_K(K) = K`.
    So `H_1` is abelian and finitely generated, hence finitely presented.
- **(2a) `H_1` preserves a proper nonzero `Q`-subspace `W`.**
  - `Lambda = W ∩ Z^3` is a primitive sublattice of rank `d in {1, 2}`. Choose
    `gamma in GL_3(Z)` with `gamma Lambda = Z^d + 0`.
  - `K = gamma H_1 gamma^-1` lies in the block upper triangular group
    `P_d(Z) = {[[A, v], [0, B]] in SL_3(Z) : A in GL_d(Z), B in GL_{3-d}(Z)}`.
    This group is an extension
    `1 -> Z^2 -> P_d(Z) -> GL_d(Z) x GL_{3-d}(Z)`, whose kernel is the block
    unipotent group and whose quotient `GL_2(Z) x {±1}` is virtually free.
  - `K ∩ Z^2` is finitely presented. The image of `K` is a finitely generated
    subgroup of a virtually free group, hence finitely presented by (iii).
  - By (i), `K`, and so `H_1`, is finitely presented.

**Consequence.** A finitely generated, not finitely presented `N <= SL_3(Z)`
is Zariski dense. `N` has infinite index, because every finite-index subgroup
of `SL_3(Z)` is finitely presented.
