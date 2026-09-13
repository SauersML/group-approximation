---
rg: 2
id: simple-el-group-middle-regime-central-extension-proof
kind: route
title: Kernels of nontrivial MF maps are central, so a trivial centre rules out a middle MF rank
target: simple-el-group-middle-regime-is-a-central-extension-effect
requires: [mf-rigidity-is-monotone-in-matrix-rank]
artifacts:
  - research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md
---

Put `G = EL_N(R)`. Two facts are used: MF passes to subgroups (`non_mf_groups_exist.tex` l.1080), and the definitions
of `mf`, `rig` and the middle regime from `mf-rigidity-is-monotone-in-matrix-rank`, which also gives `mf(R) < rig(R)`.

(a) Let `φ: G → H` be nontrivial with `H` MF. Then `ker φ` is a normal subgroup and `ker φ ≠ G`, so by hypothesis
`ker φ ≤ Z(G)`. The image `φ(G) ≅ G/ker φ` is a subgroup of `H`, hence MF.

(b) Suppose `Z(G) = 1`. If `φ` is as in (a), then `ker φ = 1`, so `G ≅ φ(G)` is MF. Conversely, if `G` is MF, the
identity of `G` is a homomorphism to an MF group, and it is nontrivial because `e_12(1) ≠ I_N` (as `1 ≠ 0`). So at
rank `N`, "MF" and "not MF-rigid" coincide, and `N` does not satisfy `mf(R) < N < rig(R)`.

(c) If `N` is in the middle regime, then `G` is not MF and not MF-rigid. So a nontrivial `φ` into an MF group exists,
and `K = ker φ ≤ Z(G)` with `G/K` MF by (a). If `K = 1`, then `G` would be MF, a contradiction. So `K ≠ 1`. `[]`

Model tests (artifact §2):
- `L_(F_2)(1,2)`: trivial centre and `rig = 2`.
- Pestov's ring over `F_2`: `mf = rig = ∞`.
- The Toeplitz–Jacobson algebra violates the hypothesis, since `EL_N(J, JeJ)` is proper and non-central, and it does
  have an infinite middle regime.
