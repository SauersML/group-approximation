---
rg: 2
id: jacobson-elementary-groups-are-lea-only-if-lef
kind: claim
title: EL_n over the Jacobson algebra is Kazhdan for n >= 3, so it is LEA only if it is LEF, and for n >= 4 it is not LEA
distinct_from:
  cohn-elementary-group-is-not-lef: that proves EL_n(J) is not LEF for n >= 4; this upgrades that to not LEA, and shows that in rank three the LEA and LEF questions coincide.
  fpbs-shalom-property-t-is-open: that is the general openness of property (T) in the space of marked groups; this applies it to the Jacobson elementary groups.
  elementary-group-property-t-over-free-algebras: that proves property (T) for EL_3 over free algebras on finite fields; this is its approximation consequence for the Jacobson quotients.
artifacts:
  - research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md
---

**ESTABLISHED** (route `jacobson-kazhdan-lea-only-if-lef-proof`; artifact Section 2). Independently re-derived by
`w4-vf-gate`: PASS, Section 31.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`.

**Statement.** Let `J = F_2<S,T | TS=1>`.
1. `EL_n(J)` has property (T) for every `n >= 3`, and so does `EL_3(F_3<S,T | TS=1>)`.
2. `EL_3(J)` is locally embeddable into amenable groups (LEA) iff it is LEF. The same holds over `F_3`.
3. `EL_n(J)` is not LEA for `n >= 4`.

**Consequence.**
* A soficity proof for `EL_3(J)` through amenable local embeddings is a LEF proof.
* Such a proof must be specific to rank three: an approximation scheme that works for `EL_n(J)` uniformly in `n` would
  make `EL_4(J)` LEF.
* Sofic approximations that are not amenable local embeddings are not excluded.
