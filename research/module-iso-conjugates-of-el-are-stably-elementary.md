---
rg: 2
id: module-iso-conjugates-of-el-are-stably-elementary
kind: claim
title: Conjugating EL_M(R) by an isomorphism R^M ≅ R^N lands in EL_{N+1}(R) after adding one free coordinate
---

Let `R` be a unital ring, and `M ≥ 2`, `N ≥ 1`. Let `X ∈ M_{N×M}(R)` and `Y ∈ M_{M×N}(R)` satisfy `XY = 1_N` and
`YX = 1_M`. Then for every `g ∈ EL_M(R)`,

```text
diag(X g Y, 1) ∈ EL_{N+1}(R).
```

So the conjugate `Φ(g) = XgY ∈ GL_N(R)` of an elementary matrix is always *stably elementary*, with one extra
coordinate. Whether `Φ(g) ∈ EL_N(R)` itself is an injective-stability question for the unstable `K_1(N, R)`.

**Consequence at the MF band.** For `R = L_K(3,4)`, `N = 3`, `M = 4`, all transvections `1 + x_i r y_j` satisfy
`diag(1 + x_i r y_j, 1) ∈ EL_4(R)`. So part 1 of `leavitt-3-4-module-iso-image-normally-generates-e3` holds iff
injective stability `GL_3(R)/EL_3(R) → GL_4(R)/EL_4(R)` holds on `Φ(EL_4(R))`.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): PASS. A E_(ic) r B = Σ_k E_(kc') x_ki r as commuting elementary factors, the commutator e_ij(r) = [e_ic(r), e_cj(1)], and Ψ(diag(g,1)) = diag(XgY,1) re-derived.**
