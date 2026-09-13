---
rg: 2
id: quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift
kind: claim
title: "An infinite Kazhdan LEF group without finite quotients has a canonical corona trace whose realizing *-homomorphism admits no ucp lift"
distinct_from:
  operator-mf-group-not-weakly-quasidiagonal-exists: that says no separating ucp approximations exist at all; this says the specific trace-realizing corona *-homomorphism built from local models cannot be lifted, even though it has the right trace.
  mf-to-weak-qd-citation-has-unproved-lifting-step: that records a missing lifting step in a citation; this shows the lifting step is impossible for these groups.
  simple-kazhdan-lef-group-c-star-fails-llp: that shows C*(S) fails the LLP abstractly; this exhibits an explicit non-liftable *-homomorphism into a norm matrix corona.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let G be a countable Kazhdan group and τ_G = tr_ω∘Φ for a unital
*-homomorphism Φ: C*_max(G) → Q_d. If Φ has a ucp lift C*_max(G) → ∏_k M_{d_k}, then G is residually
finite.

Hence, if G is infinite, LEF and Kazhdan and has no nontrivial finite quotient, the *-homomorphism of
`lef-group-canonical-trace-is-a-corona-trace` has no ucp lift, and neither does any *-homomorphism realizing
τ_G. Witnesses: G = EL_3(LC(X,F_q)⋊Z) and S = G/Z(G) for an infinite minimal subshift X.

Interpretation for the UN program. On the measure side the canonical trace is realized in the corona, but
only by a map that no completely positive approximation can follow. The quasidiagonal (liftable) world sees
only residual finiteness.

Proof route: `quotientless-lef-kazhdan-corona-trace-no-lift-proof`.
