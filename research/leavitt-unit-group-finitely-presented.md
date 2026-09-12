---
rg: 2
id: leavitt-unit-group-finitely-presented
kind: claim
title: The binary Leavitt unit group is finitely presented
distinct_from:
  finitely-presented-nonsofic-group-exists: that is existence of some finitely presented nonsofic group, witnessed by a finite-table Kazhdan cover which is not simple; this is finite presentability of the specific group L_(F_2)(1,2)^x.
  binary-leavitt-unit-word-problem-decidable: that is decidability of the word problem of the same group; this is a finite presentation, which that result neither uses nor supplies.
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

**ESTABLISHED (literature import).** For `R = L_(F_2)(1,2)` the unit group
`R^x` is finitely presented.

Source: H. V. Khanh, *General linear and Steinberg groups over the Leavitt
algebra L_{F_2}(1,2)*, arXiv:2609.08428v1 (8 September 2026), **Theorem 6.1**:
"The group G = R^× is finitely presented." The paper derives it from the
Steinberg comparison (its Theorem 5.4) and the Krstić–McCool theorem, and
records an explicit presentation as Proposition 6.2. The statement was checked
against the PDF text; the proof has not been reviewed in this repository.

The paper's ring `F_2<e,f,e*,f*>/(e*e = f*f = 1, e*f = f*e = 0, ee* + ff* = 1)`
is this repository's `L_(F_2)(1,2)` under `s_0 = e`, `s_1 = f`, `t_0 = e*`,
`t_1 = f*`.

**Practical caveat.** The presentation of Proposition 6.2 comes from a
Krstić–McCool bound and is very large; the kl-equation lane reports it is
theoretical only, and that the usable finite relator list is still the atlas
Steinberg presentation already in this graph, which with the paper's Theorem
5.4 now presents `R^x` itself. Use this claim for finite presentability, not
as a computational presentation.

Consumers: `fp-simple-nonsofic-via-leavitt-unit-group` and
`fp-simple-full-mf-radical-via-leavitt-unit-group`.
