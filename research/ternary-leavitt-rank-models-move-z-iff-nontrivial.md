---
rg: 2
id: ternary-leavitt-rank-models-move-z-iff-nontrivial
kind: claim
title: The ternary Leavitt unit group has a characteristic-three rank model moving minus one iff it has a nontrivial one iff its scalar quotient has one
distinct_from:
  anti-central-rank-models-kill-ternary-corner-witnesses: that turns a z-moving rank model of a subgroup containing z, w and d into a K_0 state; this shows moving z is automatic for the whole unit group and transfers rank models between the unit group and its scalar quotient.
  projective-ternary-group-is-f3-linear-sofic: that asks for separating approximations of the scalar quotient; this shows a single nontrivial rank model of the quotient, or of the unit group, already moves z, and converts models of the unit group into models of the quotient.
artifacts:
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Sections 1–2; independent verification requested from
`w3-vf-linear`). Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = −1`, `PG = G/<z>` and `ι(g) = s0 g t0 + s1 t1`.
A *rank model* is a homomorphism into the units of a rank ultraproduct of matrix algebras over fields of
characteristic three. The following are equivalent:

1. `G` has a rank model moving `z`;
2. `G` has a nontrivial rank model;
3. `G` has an injective rank model;
4. `PG` has a nontrivial rank model;
5. `PG` has an injective rank model;
6. `G` has a rank model sending `z` to `−1`.

Explicitly, if `σ` is nontrivial then `σ∘ι` is injective and moves `z`. If `σ(z) = −1`, then `σ⊗σ` is a
nontrivial model of `PG`, by a tensor-square rank lemma: `rk(A⊗A − I)/n^2 < 1/3` forces
`rk(A ∓ I)/n <= rk(A⊗A − I)/n^2` for one of the signs.

Consequences:
- Any nontrivial characteristic-three rank model of `G` or of `PG` refutes
  `ternary-anti-invariant-swap-corner-is-full`, through `anti-central-rank-models-kill-ternary-corner-witnesses`
  with `Γ = G`.
- Equivalently, a solution of the ternary corner equation leaves `G` and `PG` without any nontrivial
  characteristic-three rank model, so neither is `F_3`-linear sofic.
- The open gate is the single question `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`.

Proof: route `ternary-leavitt-rank-models-move-z-proof`.
