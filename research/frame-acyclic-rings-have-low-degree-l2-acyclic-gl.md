---
rg: 2
id: frame-acyclic-rings-have-low-degree-l2-acyclic-gl
kind: claim
title: If the ordered frame complex X_r(A) of an infinite ring is (r-3)-acyclic, then GL_r(A) has β_n^(2) = 0 for n <= r-3
distinct_from:
  khanh-acyclicity-and-steinberg-criteria: that is Khanh's integral acyclicity criterion, which also needs zero stabilization maps, the scalar weight lemma and K-theory input; this L²-criterion needs only frame connectivity and an infinite coefficient ring, because the unipotent normal subgroups of the stabilizers kill L²-homology at E^1.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `A` be an infinite unital ring, `r >= 3`,
and `X_r(A)` Khanh's ordered frame semisimplicial set. If `H̃_d(X_r(A); Z) = 0` for
`0 <= d <= r-3`, then `β_n^(2)(GL_r(A)) = 0` for `0 <= n <= r-3`.

**Why.** The stabilizer of a frame of `k <= r-1` vectors is conjugate to
`J = {[[I_k, b],[0, d]]}`, which contains the infinite abelian normal subgroup
`U ≅ M_(k x (r-k))(A)`. Theorem A of the artifact.

**Calibration.**
- `A = F_2` shows infinitude is needed: `GL_r(F_2)` is finite and `β_0^(2) != 0`.
- `A = Z`, `r >= 3` agrees with L²-acyclicity of lattices in `SL_r(R)`.

Route: `frame-acyclic-rings-l2-acyclic-gl-proof`.
