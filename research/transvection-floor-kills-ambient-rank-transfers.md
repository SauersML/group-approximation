---
rg: 2
id: transvection-floor-kills-ambient-rank-transfers
kind: claim
title: In every representation of SL_n(F_q) (n >= 3) in characteristic other than p, a transvection moves at least an eighth of what any element moves, so no representation of the ambient finite linear group transfers rank models across characteristics
distinct_from:
  c-linear-sofic-iff-bounded-dimension-large-characteristic: that proves tame lifting (models whose generated group has order prime to the characteristic lift to C) and kills Sylvester-rank certificates for component (a); this kills the opposite-direction tool, representation-theoretic transfer of wild models, and names the step where it dies (a transvection defect inside an SL_3 block).
  root-splits-into-large-and-fixed-characteristic-witnesses: that sorts rank ultraproducts by characteristic; this is a metric rigidity theorem for representations of finite special linear groups and bounds what any transfer between the classes can look like.
  non-large-characteristic-linear-sofic-group-exists: that is the open component (a); this establishes no witness and no equality, only that the equality L_inf = complex-linear soficity cannot be proved by a functorial transfer.
---

**ESTABLISHED (2026-09-17, lane `sw-069`, unreviewed)** by `transvection-floor-kills-ambient-rank-transfers-proof`.

Notation as on `root-splits-into-large-and-fixed-characteristic-witnesses`. `q = p^e`. A *transvection* is an element
`t` of `SL_n(F_q)` with `rank(t - 1) = 1` and `(t - 1)^2 = 0`. For a representation `psi : S -> GL_N(K)` write
`mu_psi(y) = rank(psi(y) - 1)/N` and `V^S` for the fixed space.

**Theorem 1 (transvection floor).** Let `n >= 3`, let `K` be a field of characteristic different from `p`, and let
`psi : SL_n(F_q) -> GL_N(K)` be any representation. Then for every transvection `t` and every `y` in `SL_n(F_q)`:

`rank(psi(t) - 1) >= c(p, q) (N - dim V^(SL_n)) >= c(p, q) rank(psi(y) - 1)`,  with `c(p, q) = (1 - 1/p)(1 - 1/q)/2 >= 1/8`.

The same holds for any group `Q`, any subgroup `S <= Q` isomorphic to `SL_m(F_q)` with `m >= 3`, any transvection
`t` of `S`, all `y` in `S`, and any representation of `Q` in characteristic other than `p` (restrict to `S`).

**Corollary 2 (ambient transfers fail on the infinite cyclic group).** Let `psi_n` be representations of
`GL_n(F_q)` or `SL_n(F_q)`, `n >= 3`, over fields of characteristic other than `p`. Take `W = {1, g, g^(-1)}` in `Z`,
`y` in `SL_n(F_q)` with `rank(y - 1) = n`, and the model `phi(g) = y`, `phi(g^(-1)) = y^(-1) t`. It is a
`(W, 1/n)`-model with separation `>= 1 - 1/n`. The transported model `psi_n o phi` has defect at least `1/8` of its
own separation at `g`, however large `n` is.
- So no family `psi_n` sends `(W, eps)`-models to `(W, omega(eps))`-models with separation `c > 0` and
  `omega(eps) < c/8`. This includes permutation modules on vectors, subspaces or flags, Weil and Deligne--Lusztig
  representations, and any tensor or Brauer-lift construction applied to the ambient group.
- It applies from characteristic `p` to characteristic `0` (the passage `L_p` or `L_inf` to complex-linear sofic)
  and to every other characteristic `l != p`.

**Corollary 3 (rank ultraproducts of special linear groups).** Let `Pi = prod_omega SL_(n_i)(F_(q_i)) / N_omega`
with `n_i -> infinity` along `omega` and rank length. Let `psi_i` be representations over fields `K_i` with
`char K_i != char F_(q_i)` for `omega`-most `i`, such that `(psi_i)` induces a well-defined homomorphism
`Pi -> prod_omega GL_(N_i)(K_i) / N_omega`. That homomorphism is trivial.

**Calibration.**
- *Natural module.* Over `F_q` itself, `rank(t - 1)/rank(y - 1) = 1/n`. The floor needs characteristic other than
  `p`, and fails exactly as it must in characteristic `p`.
- *Tame lifting.* The Brauer lift in `c-linear-sofic-iff-bounded-dimension-large-characteristic` is a
  representation of the generated group `Q = <phi(W)>`, of order prime to `p`. Such a `Q` contains no transvection,
  so Theorem 1 is silent there, consistently.
- *Computation.* `experiments/transvection-floor-2026-09-17/transvection_floor_check.py` enumerates `SL_3(F_2)`,
  `SL_3(F_3)`, `SL_4(F_2)` and `SL_3(F_4)` and checks the floor and the root-subgroup bound on permutation modules
  (vectors, points, lines, flags, pairs).
- *`n = 2`.* The proof uses a torus acting transitively on nonzero root elements and two opposite unipotent
  radicals generating the group; the statement is made only for `n >= 3`.

**What this changes for component (a).** The decision "`L_inf` = complex-linear soficity" now has a class kill on
each side.
- A proof that some group is not in `L_inf` cannot use Sylvester rank functions (sw-024).
- A proof of equality cannot be a transfer that is a representation of the ambient finite linear group. Any lift
  of a wild model must depend on the model's generated group `Q`. It must also fail to be a representation of `Q`
  whenever `Q` contains an `SL_3(F_q)` block through a defect transvection and a separated element.
- The live form of the equality problem is therefore a *non-homomorphic*, model-dependent lift of wild models.

**Not covered.** Rank-*approximate* representations of `SL_n(F_q)` (defect `delta` on all pairs), and lifts that use
`Q` but break its `SL_3` blocks. Rank-metric uniform stability of the finite groups `SL_n(F_q)` in characteristic
zero would extend Theorem 1 to the first class.

**Credit.** Uniform character-ratio bounds for finite groups of Lie type (Gluck; Bezrukavnikov--Liebeck--Shalev--Tiep)
imply versions of Theorem 1. The proof here is a self-contained root-subgroup count. The consequences for
rank-model transfer are new here. The novelty check was bounded.
