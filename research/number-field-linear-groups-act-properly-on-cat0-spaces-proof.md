---
rg: 2
id: number-field-linear-groups-act-properly-on-cat0-spaces-proof
kind: route
title: S-integral points are discrete in the S-adelic group, which acts properly on symmetric spaces times buildings
target: number-field-linear-groups-act-properly-on-cat0-spaces
requires: []
---

**1. Entries in S-integers.** Let `g_1, ..., g_r` generate `G`. Let `S` be the
finite set of finite places `v` of `F` at which some entry of some
`g_i^{±1}` is not integral. Then `G <= GL_m(O_(F,S))`, where `O_(F,S)` is the
ring of `S`-integers.

**2. Discreteness.** Let `V_inf` be the archimedean places, and put
`L = ∏_{v in S ∪ V_inf} GL_m(F_v)`, a locally compact group. The diagonal map
`O_(F,S) -> ∏_{v in S ∪ V_inf} F_v` has discrete image. If `x in O_(F,S)`
satisfies `|x|_v < 1` for all `v in S ∪ V_inf`, then `|x|_v <= 1` at every other
place, so `∏_v |x|_v < 1` and the product formula forces `x = 0`. Applying
this to all entries of `g` and `g^{-1}` shows that `GL_m(O_(F,S))`, and hence
`G`, is discrete in `L`.

**3. The space.** For each `v in S ∪ V_inf` let `K_v` be a maximal compact
subgroup: `O(m)`, `U(m)` or `GL_m(O_v)`. Let `X_v` be the following complete
CAT(0) space with a proper isometric `GL_m(F_v)`-action whose point
stabilizers are compact:

- `v` real: the positive definite symmetric matrices with the invariant
  Riemannian metric, `GL_m(R)/O(m) = (SL_m(R)/SO(m)) × R`, a complete
  simply connected manifold of nonpositive curvature.
- `v` complex: `GL_m(C)/U(m)`, the same with Hermitian matrices.
- `v` finite: `B_v × R`, where `B_v` is the Euclidean Bruhat–Tits building of
  `SL_m(F_v)`, a complete locally finite CAT(0) polyhedral complex. `g` acts on
  `B_v` through `PGL_m(F_v)` and on `R` by translation by `log|det g|_v`.
  Local finiteness holds because the residue field is finite. Stabilizers of
  bounded sets are compact: a bounded set of lattice classes together with a
  bounded determinant valuation meets finitely many cosets of the compact open
  subgroup `GL_m(O_v)`.

`X = ∏ X_v` is proper, finite-dimensional, complete and CAT(0), and `L` acts
on it by isometries. For every bounded `B <= X` the set
`{l in L : lB ∩ B != ∅}` is relatively compact.

**4. Properness.** A discrete subgroup meets a relatively compact set in
finitely many elements. So `G` acts properly on `X`.

**5. Z-linear case.** `GL_m(Z) <= GL_m(Q)`, and the same argument works with
`S` empty. ∎

Sources for the standard facts: Bridson–Haefliger, *Metric Spaces of
Non-Positive Curvature*, Ch. II.10 (symmetric spaces of nonpositive curvature)
and Ch. II.10A (Euclidean buildings; the Bruhat–Tits building of `SL_m` over a
local field). The chapter numbers are from memory and should be checked before
anyone quotes them.
