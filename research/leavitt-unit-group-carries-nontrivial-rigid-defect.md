---
rg: 2
id: leavitt-unit-group-carries-nontrivial-rigid-defect
kind: claim
title: The nine-leaf Leavitt configuration has a nontrivial rigid compression defect
distinct_from:
  openai-criterion-commuting-factor-is-central: that derives the abelian-factor conclusion for sofic groups; this computes, with no approximation hypothesis, that the Leavitt configuration violates it.
  openai-nine-leaf-leavitt-configuration: that asserts the hypotheses of the expander-matching criterion; this is the defect computation drawn from them.
  kun-thom-wreath-carries-rigid-defect: that is a nontrivial defect in the Kun--Thom coset wreath; this is one inside the binary Leavitt unit group.
  weak-mf-groups-can-carry-rigid-defects: that exhibits defects in operator-norm MF finite-lamp amalgams; this exhibits one in a simple finitely presented Kazhdan group.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Take the configuration of
`openai-nine-leaf-leavitt-configuration` over `R = L_(F_2)(1,2)`:
`Gamma = EL_alpha(R)`, `G_L = EL_D(R)`, `J = V_(1000)`, and the compressor `u`.

- `Gamma <= G_L <= R^x` is a rigid pair: both groups are Kazhdan, and
  `Gamma` is infranormal because `u`, `v` and `Gamma` lie in its compression
  semigroup and generate `G_L`.
- Its rigid defect is nontrivial: some `j in J` and `gamma in Gamma` satisfy

  ```text
  [u j u^-1, gamma] != 1 .
  ```

- Hence `Gamma` is not normal in `G_L`.

Derivation: `leavitt-unit-group-carries-nontrivial-rigid-defect-proof`.

Read against `sofic-groups-kill-rigid-compression-defects`, this is the defect
form of nonsoficity of `R^x`. What it adds is portability: the defect is a
statement about group elements, so it can be pulled back through a
surjection, which a nonsoficity statement cannot.
