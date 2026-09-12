---
rg: 2
id: binary-leavitt-unit-group-integrally-acyclic
kind: claim
title: The binary Leavitt unit group is integrally acyclic
distinct_from:
  leavitt-unit-group-finitely-presented: that is finite presentability of the same group, from the same paper; this is its integral homology.
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that transfers acyclicity to unit groups of B ⊗ L under K-theory hypotheses; this is the unconditional statement for L itself.
  leavitt-square-unit-group-is-fp-simple-and-acyclic: that concerns the unit group of L ⊗ L; this concerns the unit group of L.
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

**ESTABLISHED (literature import).** For `R = L_(F_2)(1,2)`,

```text
H_n(R^x; Z) = 0     for every n > 0.
```

Source: H. V. Khanh, arXiv:2609.08428v1, **Theorem 4.4**, verbatim: "The unit
group of R = L_F2(1,2) is integrally acyclic. More generally,
H_n(GL_r(R), Z) = 0 for every n > 0 and r ≥ 1." The statement and the proof
chain were checked by the literature lane (artifact).

**Consequence used downstream.** `R^x` is perfect and has trivial Schur
multiplier. By universal coefficients,
`H^2(R^x; A) = Hom(H_2, A) ⊕ Ext(H_1, A) = 0` for every abelian group `A` with
trivial action. So every central extension of `R^x` splits as a direct
product.
