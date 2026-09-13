---
rg: 2
id: non-finite-field-linear-sofic-group-exists
kind: claim
title: Some countable group is not linear sofic over finite fields
distinct_from:
  non-linear-sofic-group: that asks for a group failing linear soficity over one fixed field; this asks for a group embedding in no rank-metric ultraproduct of groups GL_n(F_q) with the finite fields allowed to vary, which is stronger than failure over any single finite field and gives failure over C.
  non-weakly-sofic-group-exists: that is Glebsky--Rivera Conjecture 4.5 about arbitrary finite groups with invariant lengths; this is about rank lengths over finite fields, and the two existence statements are equivalent by non-weakly-sofic-iff-non-finite-field-linear-sofic-group.
---

**OPEN.** There is a countable group `Gamma` that embeds in no metric ultraproduct `prod_omega GL_(n_i)(F_(q_i)) / N_omega`
with the normalized rank length `rk(g - 1)/n_i`, over any sequence of finite fields (definition on
`simple-group-psl-width-is-finite-field-linear-soficity`).

## Attempts

- **Equivalent to the Glebsky--Rivera root (2026-09-13, lane `ex3-weak-sofic-fg-dichotomy`, unreviewed).** By
  `non-weakly-sofic-iff-non-finite-field-linear-sofic-group`, this claim holds iff `non-weakly-sofic-group-exists` holds.
  A witness can be taken finitely generated and simple, since Schupp's envelope of a finitely generated witness is again
  a witness.
- **Relation to fixed-field linear soficity.**
  - A witness here is not `C`-linear sofic, because Arzhantseva--Paunescu Theorem 8.2 and Observation 8.4 (as recorded on
    `non-linear-sofic-group`) pass `C`-linear soficity to finite fields of varying characteristic. It is also not
    `F_q`-linear sofic for any fixed `q`.
  - The converse fails as a method. The characteristic-two Kaplansky route on `non-linear-sofic-group` (a one-sided
    inverse pair in `F_2[G]`) kills rank models only in characteristic two, so it cannot produce a witness here.
- **Candidates.**
  - The binary Leavitt unit group `R^x` is finitely presented, simple, Kazhdan and nonsofic. By
    `fp-simple-weak-soficity-is-finite-field-linear-soficity` it is a witness iff it is not weakly sofic.
  - The simple Kazhdan envelope of the Kun--Thom wreath is a witness iff it is not weakly sofic.
- **Dead mechanism.** Transcribing the Kun--Thom nonsoficity proof fails in every rank row over every field
  (`non-linear-sofic-group`, Attempts). The Kun--Thom wreath is weakly sofic and carries a rigid defect, so rigid
  defects alone cannot certify a witness.
