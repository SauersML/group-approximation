---
rg: 2
id: sl3-rigidity-stops-before-inner-adjoint-correction
kind: claim
title: Published SL3 rigidity does not correct the regular inner-adjoint sector
distinct_from:
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that disproves ordinary and local same-dimension stability for arbitrary challenges; this audits the narrower canonical-character inner-adjoint challenge and explains why those negative theorems do not decide it.
  character-rigidity-equals-hyperfinite-hs-stability: that is the positive primary theorem; this identifies why its amenable-limit hypothesis excludes the regular character of SL3.
  sl3-z-weakly-ucp-stable: that is the open flexible correction claim on all hyperlinear approximations; this isolates the still narrower regular inner-adjoint condition actually needed by the projective sector.
---

For `Lambda=SL_3(Z)`, the primary literature gives the following exact
boundary.

1. Becker--Lubotzky, arXiv:1809.00632, prove that every infinite
   hyperlinear property-(T) group fails strict normalized-HS stability.
   Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155v2, Theorem 6.1,
   strengthen this to failure of local HS stability.  These theorems rule
   out correcting **all** challenges, but do not identify their bad
   challenges with regular-character adjoint tuples nor rule out projective
   correction inside the inner locus.
2. Dogon--Vigdorovich, arXiv:2506.20843v2, prove that for the relevant
   higher-rank lattices character rigidity is equivalent to HYPERFINITE
   HS stability and robust `(T;FD)`.  Character rigidity is known for
   `SL_3(Z)`, but the regular character has GNS algebra `L(SL_3(Z))`, which
   is nonamenable and therefore nonhyperfinite.  The theorem deliberately
   does not correct this trace sector.
3. Character rigidity only says that the limiting character is the allowed
   regular character; it does not classify or lift the different embeddings
   of `L(SL_3(Z))` into a matrix ultraproduct.  In particular it supplies no
   reason for an exact correction of `Ad(sigma_n)` to land in the inner-
   conjugation locus isolated by
   `sl3-regular-projective-correction-is-inner-adjoint-stability`.

Thus the canonical hypothesis does not activate any published correction
theorem.  The precise missing condition is:

> Every regular-character inner-adjoint almost representation of
> `SL_3(Z)` is normalized-HS close to an honest representation that remains
> inner adjoint (equivalently, the original tuple is projectively close to a
> projective representation).

This is a restricted regular/projective HS-stability problem.  It is
implied by the stronger open flexible correction claims already in Cairn,
but is not equivalent to full HS stability and is not refuted by the known
strict/local instability theorems.  It also does not itself prove the
denominator conclusion `(UNC2)`; a direct arithmetic argument could bypass
correction.  No such result appears in the three primary sources above.
