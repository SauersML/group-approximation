---
rg: 2
id: quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift
kind: claim
title: "An infinite Kazhdan LEF group without finite quotients has a canonical MF trace whose realizing *-homomorphism admits no ucp lift"
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

**Naming and credit (review 2026-09-13, un-verify-measure, relaying un-novelty).** A *corona trace* is exactly an MF trace in the sense of C. Schafhauser, *MF traces and the Cuntz semigroup*, arXiv:1705.06555. Its abstract, read at review: "A trace τ on a separable C*-algebra A is called matricial field (MF) if there is a trace-preserving morphism from A to Q_ω". For separable C*_max(G) the two definitions agree, and the graph's MF-trace nodes (`hyperlinear-trace-not-mf-trace`, `faithful-mf-models-realize-all-mf-traces`) use the same notion. Node ids keep the word `corona`; read it as MF trace.

**Review (un-verify-measure, 2026-09-13): PASS, with a naming fix.** The subsequence extraction and the witnesses re-derived. See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T4.
