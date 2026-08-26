---
rg: 2
id: normal-kernel-restriction-rigidity-for-map-free-quotients
kind: claim
title: Two finite-dimensional unitary representations of a group that agree on a normal subgroup whose quotient has no finite-dimensional representations agree everywhere, because the intertwiner space carries a representation of the quotient
distinct_from:
  finitely-generated-map-groups-are-residually-finite: that supplies the hypothesis (a finitely generated simple nonsofic quotient has no finite-dimensional representations); this is the rigidity of restriction to the kernel that the hypothesis forces.
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: that exhibits exact vertex representations agreeing on the amalgamated Kazhdan subgroup yet far apart on an actor -- possible because that subgroup has infinite index and the quotient is not a group; this is the opposite phenomenon for a NORMAL kernel with a representation-free quotient, where agreement on the kernel forces global agreement.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

Let `K` be a normal subgroup of a group `F` such that `Q = F/K` has no
nontrivial finite-dimensional unitary representation (e.g. `F` free of finite
rank and `Q` a finitely generated simple nonsofic quotient, by
`finitely-generated-map-groups-are-residually-finite`).  For finite-dimensional
unitary representations `u, v` of `F` on `H`, let `F` act on `HS(H)` by
`Pi(f)(T) = u(f) T v(f)^*` and put `V = Hom_K(v, u) = {T : u(k) T = T v(k), k in K}`.

**Theorem.**  (1) `V` is `Pi(F)`-invariant and `Pi|_V` factors through `Q`.
(2) If `u|_K = v|_K` then `u = v`.  (3) Hence restriction
`Hom(F, U(d)) -> Hom(K, U(d))` is injective for every `d`.
(4) (Kernel absorption.)  For every finite-dimensional unitary `u` of `F`,
`u(K)' = u(F)'`, equivalently `u(K)'' = u(F)''`: the kernel generates the
same algebra as the whole group, and `u|_K` has the multiplicity structure of
`u`.  Consequently the exact `K`-commutant sector of the left-right
representation `Pi(f)(T) = u(f) T u(f)^*` is fixed pointwise by `Pi(F)`, so
it can never carry the defect sought in
`intertwiner-retention-makes-leavitt-quotient-hyperlinear`; the retained
sector must lie strictly outside every exact commutant.  This is the
finite-dimensional twin of `amenable-kazhdan-models-absorb-compression` and
of `sl3-atomic-ambient-is-absorbed-by-lattice`.

(1) is a two-line computation using normality of `K`; (2) follows because
`1 in V` and the `Q`-representation on `V` is trivial, so `1 = Pi(f)(1) =
u(f) v(f)^*`.  The content of the statement is its contrast with
`leavitt-presentation-double-forces-restriction-instability`: exact agreement
on `K` is rigid in every dimension, but approximate agreement is not
uniformly so across dimensions.
