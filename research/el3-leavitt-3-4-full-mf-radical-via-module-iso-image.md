---
rg: 2
id: el3-leavitt-3-4-full-mf-radical-via-module-iso-image
kind: route
title: If the conjugate of EL_4 lies in EL_3 and normally generates it, the rank-four MF radical descends to rank three
target: el3-leavitt-3-4-has-full-mf-radical
requires: [leavitt-3-4-module-iso-image-normally-generates-e3, non-ibn-ring-el-n-full-mf-radical-above-module-rank]
artifacts: [research/artifacts/un-low-rank-band-noncompletable-columns-2026-09-13.md]
---

Let `R = L_K(3,4)`, and `X, Y` with `XY = 1_3`, `YX = 1_4`. Put `Φ(g) = XgY`. Let `φ : EL_3(R) → M` be a
homomorphism with `M` an MF group.

1. By `leavitt-3-4-module-iso-image-normally-generates-e3` (part 1), `Φ(EL_4(R)) ⊆ EL_3(R)`. So `φ∘Φ` restricted to
   `EL_4(R)` is a homomorphism `EL_4(R) → M`.
2. `R^3 ≅ R^4`, so `non-ibn-ring-el-n-full-mf-radical-above-module-rank` (with `m = 3`, `d = 1`, `N = 4 ≥ m+1`) makes
   every homomorphism from `EL_4(R)` to an MF group trivial. Hence `Φ(EL_4(R)) ⊆ ker φ`.
3. `ker φ` is normal in `EL_3(R)`, so it contains the normal closure of `Φ(EL_4(R))`. That closure is `EL_3(R)` by part
   2 of the required claim. So `φ` is trivial. ∎

This route does not fire while `leavitt-3-4-module-iso-image-normally-generates-e3` is open.
