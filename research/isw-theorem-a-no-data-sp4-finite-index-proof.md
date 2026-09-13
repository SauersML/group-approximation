---
rg: 2
id: isw-theorem-a-no-data-sp4-finite-index-proof
kind: route
title: Finitely many realizable classes of Gamma' force a constant class which pointwise closedness kills
target: isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups
requires:
  - sp4-finite-index-fd-projective-multiplier-is-finite
---

Suppose `c_n in Z^2(Gamma',T)` satisfies `(NA1')` for a finite-index
`Gamma' <= Sp_4(Z)` and some `Lambda <= Gamma'`.

**A constant class.**  By `(NA1')(3)` every class `[c_n]` lies in
`R(Gamma')`, which is finite by
`sp4-finite-index-fd-projective-multiplier-is-finite`.  Pass to a
subsequence on which `[c_{n_k}] = [c]` is constant.  Then
`c_{n_k} in c . B^2(Gamma',T)` for one fixed cocycle `c`.

**Coboundaries are pointwise closed.**
- The cochain space `T^Gamma'` is compact (Tychonoff).
- `delta` is continuous in the product topology.
- `Z^2(Gamma',T)` is Hausdorff.
- So `B^2(Gamma',T) = delta(T^Gamma')` is compact, hence closed.  This is
  the observation of `sp4-metaplectic-class-pointwise-coboundary-limit`,
  which holds for every discrete group.
- Translation by `c` is a homeomorphism, so `c . B^2(Gamma',T)` is closed.

**Contradiction.**
- By `(NA1')(2)`, `c_{n_k} -> 1`.  Hence `1 in c . B^2`, i.e. `[c] = 0`.
- So each `c_{n_k} = delta b_k` is a coboundary of `Gamma'`.
- Its restriction `delta(b_k|_Lambda)` is then a coboundary of `Lambda`,
  contradicting `(NA1')(1)`.

`Lambda` was arbitrary, so the fence is uniform in the subgroup.

This is the argument of `isw-theorem-a-has-no-data-on-sp4-lattice-proof`
with `Gamma'` in place of `Gamma`.  All of the new content sits in the
finiteness input.
