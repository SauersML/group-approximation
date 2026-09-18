---
rg: 2
id: z-localized-fp-rf-from-hecke-overgroup
kind: route
title: A finitely presented Hecke overgroup of SL_2(Z_(l)) is a finitely presented residually finite group containing Z_(l)
target: z-localized-embeds-in-fp-rf-group
requires:
  - sl-2-z-localized-has-fp-hecke-overgroup
---

Let `l, Λ, ι` be as in `sl-2-z-localized-has-fp-hecke-overgroup`.
- `Λ` is finitely presented.
- `Λ` is residually finite: by (H4) some group in `BS_Λ` acts faithfully on a locally
  finite tree, its vertex stabilizers are residually finite, and they are
  commensurable with `Λ`. This is the first bullet of "What any witness must look
  like" in that node.
- The unipotents `[[1,c],[0,1]]`, `c in Z_(l)`, form a copy of `Z_(l)` in
  `A = SL_2(Z_(l))`, and `ι` is injective on `A`. ∎
