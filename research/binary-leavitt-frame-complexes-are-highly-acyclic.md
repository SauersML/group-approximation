---
rg: 2
id: binary-leavitt-frame-complexes-are-highly-acyclic
kind: claim
title: The ordered frame complex X_r of the binary Leavitt algebra is (r-3)-acyclic
distinct_from:
  khanh-acyclicity-and-steinberg-criteria: that bundles Khanh's acyclicity and Steinberg criteria for arbitrary rings; this is the connectivity of the frame complexes of L_(F_2)(1,2) itself, his Corollary 4.3, which is the geometric hypothesis those criteria need.
  binary-leavitt-unit-group-integrally-acyclic: that is the integral homology of the unit group; this is the homology of the complex the group acts on.
---

**ESTABLISHED (literature import).** Let `R = L_(F_2)(1,2)`. The ordered frame
semisimplicial set `X_r(R)` has as `p`-simplices the tuples `(v_1, ..., v_k)`, `k = p + 1 <= r`,
for which `R^r = v_1 R ⊕ ··· ⊕ v_k R ⊕ C` with `C ≅ R^(r-k)` and each `a ↦ v_i a` an
isomorphism onto `v_i R`. Faces delete vectors. Then:
- `H̃_d(X_r(R); Z) = 0` for `r >= 3` and `0 <= d <= r-3`;
- `GL_r(R)` acts transitively on the `(k-1)`-simplices, and stabilizers fix simplices
  pointwise.

Route: `binary-leavitt-frame-complexes-acyclic-citation`.
