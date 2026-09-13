---
rg: 2
id: jacobson-kazhdan-lea-only-if-lef-proof
kind: route
title: A Kazhdan neighbourhood contains only finite amenable groups
target: jacobson-elementary-groups-are-lea-only-if-lef
requires:
  - elementary-group-property-t-over-free-algebras
  - steinberg-finite-presentation-and-kazhdan-theorem
  - fpbs-shalom-property-t-is-open
  - cohn-elementary-group-is-not-lef
artifacts:
  - research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md
---

**Derivation** (artifact Section 2).

1. **Property (T), rank three.**
   - `J` and `J_(F_3)` are quotients of free algebras on two generators, so `EL_3` over them is a quotient of `EL_3`
     over a free algebra.
   - That group is Kazhdan (`elementary-group-property-t-over-free-algebras`), and quotients of Kazhdan groups are
     Kazhdan.
2. **Property (T), rank at least four.** `EL_n(J)` is a quotient of `St_n(J)`, which is Kazhdan
   (`steinberg-finite-presentation-and-kazhdan-theorem`).
   - Both items agree with Ershov--Jaikin-Zapirain, Invent. Math. 179 (2010) 303--347, whose abstract was read
     2026-09-12.
3. **LEA implies LEF.** By `fpbs-shalom-property-t-is-open`, a Kazhdan marked group has a neighbourhood of Kazhdan
   groups.
   - Amenable Kazhdan groups are finite, so a limit of amenable marked groups is a limit of finite ones.
4. **Rank at least four.** `EL_n(J)` is not LEF (`cohn-elementary-group-is-not-lef`), so it is not LEA.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 31.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
