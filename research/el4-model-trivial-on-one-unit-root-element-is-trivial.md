---
rg: 2
id: el4-model-trivial-on-one-unit-root-element-is-trivial
kind: claim
title: A homomorphism of EL_4(R) that kills one unit root element is trivial, and over a simple ring one that kills any nonzero root element
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL_n with EL_n over the binary Leavitt algebra and proves the unit group perfect; this is a normal-closure statement about EL_4 over any ring, used to pass triviality from the EL_3 block of an EL_4 model to the whole group.
  el3-unit-root-matrix-units-iff-two-root-identities: that characterizes when the six EL_3 unit root elements act by matrix units; this says a model moving nothing on one root subgroup moves nothing at all.
  matrix-unit-rank-models-extract-ring-rank-models: that extracts a ring rank model from a matrix-unit EL_3 model or finds it trivial; this carries the triviality of the EL_3 block up to EL_4(R).
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

**ESTABLISHED** (proof route `el4-model-unit-root-triviality-proof`).

Let `R` be a unital ring, `G` a group and `sigma : EL_4(R) -> G` a homomorphism.
1. If `sigma(x_IJ(1)) = 1` for one pair `I != J`, then `sigma` is trivial.
2. If `R` is simple and `sigma(x_IJ(r)) = 1` for one pair `I != J` and one `r != 0`, then `sigma` is
   trivial.

**Consequences for family R4.**
- **Block to whole group.** An `EL_4(R)` model that is trivial on the upper-left `EL_3(R)` block is
  trivial. This is the step the route `leavitt-el3-triviality-via-rank-four-cuntz-family` needs, in
  its `D = 0` branch, to pass from "the block is trivial" to "the model is trivial".
- **Every root operator moves.** A model with nonzero two-root defect `D = n_23(1) n_12(1)` is
  nontrivial, so every root operator `n_IJ(r)` with `r != 0` is nonzero over the simple Leavitt
  algebra. So any corner idempotent that absorbs such an operator on one side has positive rank. That
  is check (iii) of `rank-four-isometry-relations-give-corner-cuntz-family`.

## Attempts

Established, not open. The proof is a twelve-step chain of Steinberg commutators
`[x_ab(r), x_bc(s)] = x_ac(rs)` inside the normal closure (artifact Section 2, Lemma 3).
