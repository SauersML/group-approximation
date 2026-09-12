---
rg: 2
id: leavitt-unit-group-is-simple-fa-nonsofic-proof
kind: route
title: Bundle finite presentation, simplicity, nonsoficity and property FA from the Kazhdan cover
target: leavitt-unit-group-is-simple-fa-nonsofic
requires:
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
  - openai-leavitt-unit-nonsofic
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
  - property-t-implies-property-fa
artifacts:
  - research/artifacts/gottschalk-other-hosts-2026-09-12.md
---

## Direct proof

Write `R^x = L_{F_2}(1,2)^x`.

- **Finitely presented.** `leavitt-unit-group-finitely-presented`.
- **Simple.** `binary-leavitt-unit-group-is-simple`.
- **Not sofic.** `openai-leavitt-unit-nonsofic`.
- **Property FA.** By `hyperbolic-kazhdan-cover-of-leavitt-unit-group` there is a
  hyperbolic Kazhdan group `H` and a surjection `H ->> R^x`. Property (T) passes
  to homomorphic images (if `H` has (T) and `H ->> Q`, then `Q` has (T);
  standard), so `R^x` has property (T). Then `property-t-implies-property-fa`
  (Watatani) gives that `R^x` has property FA.

So `R^x` is finitely presented, simple, property FA and not sofic, i.e. a group
`Sigma` of the kind excluded from the sofic-permanence closure. No step decides
surjunctivity of `R^x`.
