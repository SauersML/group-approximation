---
rg: 2
id: nonamenable-factorization-groups-have-nonexact-full-cstar
kind: claim
title: A nonamenable factorization-property group has nonexact full group C-star algebra
distinct_from:
  nonamenable-factorization-regular-quotient-not-liftable: that identifies the failed local lifting of the full-to-reduced quotient; this extracts the intrinsic nonexactness consequence for the full algebra.
  exact-gns-kernel-amenability-reduction: that is a positive theorem under exactness; this is its sharp group-algebra contrapositive.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

**THEOREM.**  If a discrete group `G` is nonamenable and has Kirchberg's
factorization property, then `C*_(max)(G)` is not exact.

Indeed, factorization makes the full canonical trace amenable.  If the full
algebra were exact, the Effros--Haagerup local lifting theorem would locally
lift its regular/GNS quotient onto `C*_r(G)`; amenability would descend to
the faithful reduced canonical trace.  A central extension of that trace to
`B(ell^2 G)`, restricted to the diagonal `ell^infinity(G)`, is a
left-translation-invariant mean.  This would make `G` amenable, a
contradiction.
