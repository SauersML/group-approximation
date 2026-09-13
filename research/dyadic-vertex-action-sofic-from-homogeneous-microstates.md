---
rg: 2
id: dyadic-vertex-action-sofic-from-homogeneous-microstates
kind: route
title: Microstates of the frame spaces of a quaternionic tower give orbit charts for the dyadic vertex action
target: dyadic-bruhat-tits-vertex-action-is-sofic
requires:
  - homogeneous-quotient-soficity-gives-vertex-soficity
  - dyadic-homogeneous-quotient-admits-topological-microstates
---

Take `L = PSL_2(Q_2)`, `K` the image of `SL_2(Z_2)`, `A = PSL_2(Z[1/2])` and `C = PSL_2(Z)`.
Then `A ∩ K = C`. Choose a torsion-free cocompact lattice `Λ_1 <= L`, for instance the image of a
torsion-free finite-index subgroup of a definite quaternion unit group split at `2`. Let `Λ_N` be
the intersection of all subgroups of `Λ_1` of index at most `N`. These are finite-index normal
subgroups, they decrease, and they intersect in `{1}` by residual finiteness. Every `Λ_N` is
torsion free and cocompact. The required claim
`dyadic-homogeneous-quotient-admits-topological-microstates` supplies the microstates `(HV1)` on
every `L/Λ_N`, and item 1 of `homogeneous-quotient-soficity-gives-vertex-soficity` then gives
soficity of `A ↷ A/C`. This is the target, the action on one colour class of vertices of the
`3`-regular tree.

In tree language the orbit chart at a microstate vertex `v` is as follows. The mark `y(v)` is a
frame, that is, a covering `T → Λ_N\T`. The chart sends a window vertex to its image under this
covering. Separation is `girth(Λ_N\T) > diam(E)`, and covariance is metric closeness of the marks.
