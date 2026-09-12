---
rg: 2
id: nonexact-full-cstar-from-regular-quotient
kind: route
title: Exactness would locally lift the forbidden regular quotient
target: nonamenable-factorization-groups-have-nonexact-full-cstar
requires:
  - nonamenable-factorization-regular-quotient-not-liftable
  - exact-gns-kernel-amenability-reduction
artifacts:
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

Let `G` be nonamenable with the factorization property and suppose that
`A=C*_(max)(G)` were exact.  Exactness passes to the regular quotient
`A/J=C*_r(G)`; the Effros--Haagerup theorem used in
`exact-gns-kernel-amenability-reduction` makes the quotient map locally
liftable.  This contradicts
`nonamenable-factorization-regular-quotient-not-liftable`.

Equivalently, one may repeat the trace argument directly: factorization
makes the full canonical trace amenable, local liftability descends it to the
reduced algebra, and a reduced hypertrace restricts to an invariant mean on
`ell^infinity(G)).
