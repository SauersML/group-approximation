---
rg: 2
id: isw-theorem-a-has-no-data-on-sp4-lattice-proof
kind: route
title: Finitely many realizable classes force a constant-class subsequence which pointwise closedness kills
target: isw-theorem-a-has-no-data-on-sp4-lattice
requires:
  - sp4-fd-projective-multiplier-is-finite
  - sp4-metaplectic-class-pointwise-coboundary-limit
---

Suppose `c_n in Z^2(Gamma,T)`, `Gamma = Sp_4(Z)`, satisfies (NA1).

By hypothesis (3), every class `[c_n]` lies in the subgroup `R` of
finite-dimensionally realizable classes, which is FINITE by
`sp4-fd-projective-multiplier-is-finite`.  Pass to a subsequence with
`[c_{n_k}] = [c]` constant, so `c_{n_k} in c . B^2(Gamma,T)` for a
fixed cocycle `c`.

The set `c . B^2(Gamma,T) = c . delta(T^Gamma)` is the image of the
compact space `T^Gamma` (Tychonoff) under a continuous map into the
Hausdorff product space `T^{Gamma x Gamma}`, hence compact and closed —
this is the translation by `c` of the closedness of `B^2(Gamma,T)`
proved in `sp4-metaplectic-class-pointwise-coboundary-limit`
(translation by a fixed cocycle is a homeomorphism of
`Z^2(Gamma,T)`).

By hypothesis (2), `c_{n_k} -> 1` pointwise, so `1 in c . B^2(Gamma,T)`,
i.e. `[c] = 0`.  Then each `c_{n_k}` is a coboundary of `Gamma`,
`c_{n_k} = delta b`, and its restriction to `Lambda` is the coboundary
`delta(b|_Lambda)` — contradicting hypothesis (1).  No sequence
satisfying (NA1) exists.  Since `Lambda` was arbitrary, the fence is
uniform in the subgroup.
