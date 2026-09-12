---
rg: 2
id: ternary-leavitt-rank-models-move-z-proof
kind: route
title: Pull any nontrivial model back along the corner embedding, compress to the minus-one corner, and square it to reach the scalar quotient
target: ternary-leavitt-rank-models-move-z-iff-nontrivial
requires: [leavitt-units-embed-in-their-scalar-quotient, odd-leavitt-unit-groups-mod-scalars-are-fp-simple, leavitt-gl-equals-el-and-perfect-unit-group]
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md
---

## Why sufficient

- **Normal subgroups.** `PG` is simple and `G` is perfect, so every normal subgroup of `G` is `G` or lies in
  `<z>` (artifact Lemma 1.1).
- **Nontrivial to injective.** A nontrivial model `σ` has `ker σ <= <z>`. The corner embedding `ι` is
  injective and `ι(G)` meets the scalars only in `1`, so `σ∘ι` is injective and moves `z`.
- **Moving `z` to anti-central.** `f = 2(1 − σ(z))` is a nonzero central idempotent of the image, and the
  compression to the renormalized corner `fMf` sends `z` to `−1`.
- **Anti-central to the quotient.** `σ⊗σ` is a rank model with `z -> 1`. If it were trivial, the
  tensor-square rank lemma (artifact Lemma 1.2) would put `σ(G)` inside `{±1}`, giving a homomorphism
  `G -> {±1}` that is trivial by perfection, contradicting `σ(z) = −1`.
- **Quotient back to the group.** `PG` is simple, so a nontrivial model of `PG` is injective, and composing
  with the injective `π∘ι` gives an injective model of `G`.

The cycle of implications is written out in artifact Section 2.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 53 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS, including the tensor-square rank lemma with threshold `1/3`. The assigned verifier remains `w3-vf-linear`.*

*Verification by `w3-vf-linear` (2026-09-12), Section 11.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: Lemma 1.2(b) (Jordan count, 2δ < 1−δ), (c), and all implications of Theorem 2.1. Simplicity of PG enters only in Lemma 1.1 and (4)⟹(5).*
