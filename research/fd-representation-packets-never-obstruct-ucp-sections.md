---
rg: 2
id: fd-representation-packets-never-obstruct-ucp-sections
kind: claim
title: Every finite packet of finite-dimensional representations admits a compatible unital self-adjoint section
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  finite-reservoir-compactness-lifts-ucp-repairs: that upgrades packetwise repairs to one exact ucp lift, and needs them to live in a single finite-dimensional reservoir; this supplies the repairs unconditionally with no control whatever on where they live, and is exactly why that uniformity is the whole content there.
  compression-defect-dies-in-finite-dimensions: that kills a compression-centralizer defect in every finite-dimensional representation of a specific construction; this is a lifting statement about an arbitrary quotient of an arbitrary unital algebra and asserts nothing about any defect vanishing.
  km-triangle-local-bimodules-have-finite-nonflat-models: that exhibits finite-dimensional models in which the triangle's local bimodule data is nonflat; this proves that no finite family of finite-dimensional representations can obstruct a section, so the two together say nonflat finite models exist and cannot decide the lifting question.
---

**ESTABLISHED.**  Let `A` be unital, `I` a closed two-sided ideal,
`q:A->>Q=A/I`, and `E subset Q` a finite-dimensional operator system.  Let
`rho_1,...,rho_m` be **any** finite family of finite-dimensional
representations of `A`.  Then there is a unital self-adjoint linear section

```text
s:E->A,      q s = id_E,                                    (FP1)
```

such that `rho_j o s` is ucp for every `j=1,...,m`.

Proof: `fd-representation-packets-never-obstruct-proof`.

**Consequence: finite-dimensional data can never be the obstruction.**  No
computation with a finite packet of finite-dimensional representations can
refute local ucp splitting of `0 -> I -> A -> Q -> 0`, and no accumulation of
such computations can prove it.  Repeated finite-dimensional counterpacket
calculations coming out perfectly compatible is therefore the expected
outcome, not evidence: it is a theorem that they must.

This does not devalue finite nonflat models such as
`km-triangle-local-bimodules-have-finite-nonflat-models`; it locates what they
can decide.  They show a *fixed* candidate section fails at finite level.  They
cannot show every section fails, because the section may be re-chosen per
packet -- and by `(FP1)` a successful re-choice always exists.

**What a genuine failure of local splitting must look like.**  It must be an
infinite coherence failure: the correcting directions in `I` demanded by the
packets must escape every fixed finite-dimensional subspace of `I` as the
packet grows.  That is precisely the negation of the hypothesis of
`finite-reservoir-compactness-lifts-ucp-repairs`, which is why that lemma and
this one are the two halves of one dichotomy, and why the open content sits at
`finite-relator-reservoir-repairs-every-fd-packet` -- a statement about word
depth, not about any single representation.
