---
rg: 2
id: leavitt-unit-hosts-commutative-matrix-exclusion-proof
kind: route
title: Finitely generated linear quotients are residually finite, and these unit groups have no residually finite nontrivial quotient
target: leavitt-unit-hosts-exclude-matrices-over-commutative-rings
requires:
  - binary-leavitt-unit-group-is-simple
  - leavitt-unit-group-finitely-presented
  - leavitt-prime-field-units-generated-by-v-and-one-transvection
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**Proof.** Artifact Section 2.

1. **Finite generation.**
   - `L_(F_2)(1,2)^x` is finitely presented (`leavitt-unit-group-finitely-presented`).
   - `G_3 = ⟨V, x⟩` for one transvection `x` (`leavitt-prime-field-units-generated-by-v-and-one-transvection`), and
     `V` is finitely generated.
2. **Malcev.** A finitely generated subgroup of `GL_n(C)` over a commutative ring `C` is residually finite. This is
   used at statement level and was not re-read.
3. **Binary case.** `ρ(G)` is `1` or `≅ G`, because `G` is simple. An infinite simple group has no proper
   finite-index normal subgroup, so it is not residually finite. Hence `ρ` is trivial.
4. **Ternary case.** Every normal subgroup lies in `{±1}` or equals `G_3`, so the quotients are `G_3`,
   `G_3/{±1}` and `1`. The nontrivial two are infinite with no proper finite-index normal subgroup. So `ρ` is
   trivial and `ρ(z) = 1 ≠ -1` in characteristic 3.
