---
rg: 2
id: small-ball-criterion-gives-contractible-rips-complexes
kind: claim
title: Zaremsky's small-ball criterion for contractible Vietoris-Rips complexes of integer metric spaces
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for the single space (Z^n, d_1); this is a general sufficient condition on an integer metric space, which Zaremsky uses to reprove it
---

Let `(X, d)` be a metric space such that all distances are integers and, for each
`t ∈ N`, the subsets of diameter `t` have uniformly bounded cardinality. Fix `t_0`
and suppose that for every `t > t_0` there is `r_t < t` such that every `S ⊆ X` of
diameter `t` lies in some closed ball of radius `r_t`, and moreover some such ball has
its centre within `t` of the centre of every other such ball. Then `VR_{t_0}(X)` is
contractible, and so is `VR_t(X)` for every `t > t_0`.

Here `VR_t(X)` has the finite subsets of pairwise distance `≤ t` as simplices.

Literature import: `zaremsky-small-ball-rips-criterion-citation`.
