---
rg: 2
id: stw99-problem-xxv-unique-trace-sr1-z-stable
kind: claim
title: Simple nuclear unique-trace algebras of stable rank one are Z-stable (STW Problem XXV)
root: true
distinct_from:
  stw99-problem-xviii-toms-winter-conjecture: that starts from strict comparison; this starts from stable rank one plus unique trace, and by CETW plus Sato it is equivalent to deducing strict comparison from those hypotheses.
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
  - research/artifacts/stw25-real-rank-zero-k0-audit-2026-08-30.md
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

**Problem XXV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Must
a simple separable nuclear non-elementary C\*-algebra with a unique
trace and stable rank one be `Z`-stable?  Motivated by: Villadsen type I
algebras and simple `C(X) ⋊ Z^d` all have sr1 and can be
non-`Z`-stable, but the known such counterexamples all have huge
(Poulsen) trace simplices (Elliott--Li--Niu).

## Attempts

* Sharp reformulation (this session): a unique trace is a singleton compact
  zero-dimensional extreme boundary.  The established
  `stw18-finite-trace-boundary-toms-winter`
  theorem therefore gives strict comparison `=>` `Z`-stability, while
  `Z`-stability always gives strict comparison.  Equivalently, one may use
  unique-trace uniform Gamma and CETW.  Thus the problem is EXACTLY: does
  stable rank one plus a unique trace force strict comparison?  Divisibility
  is also free: sr1 gives all ranks occur (Thiel), so the algebra is pure iff
  it has strict comparison.
* Equivalently by Blackadar--Handelman duality territory: with one
  quasitrace `τ`, strict comparison means `d_τ(a) < d_τ(b) ⟹ a ≾ b` —
  failure is perforation in `Cu(A)` visible to no trace.  Unique-trace
  perforation with sr1 is unknown: Villadsen perforation lives on
  higher-dimensional trace data (`K_0` classes separated only by other
  traces... none here) so a counterexample needs perforation of purely
  cohomological origin with a single trace — the type II Villadsen
  algebras (unique trace, perforated) have HIGHER stable rank, and STW
  note the sr1/perforation coexistence with unique trace has no known
  instance.  Frontier: either prove sr1 + unique trace ⟹ unperforated
  (a Cuntz-semigroup cancellation statement in the spirit of Thiel's
  rank theorem, plausibly attackable with APRT machinery), or build a
  unique-trace Villadsen-type algebra with sr1, which requires evading
  Rordam's sr1 ⟹ cancellation-adjacent constraints at the Euler-class
  level.
* The real-rank-zero region now has an exact answer.
  `stw25-real-rank-zero-k0-perforation-is-exact-obstruction` proves that,
  under the hypotheses of XXV and real rank zero,

  ```text
  A is Z-stable  iff  K_0(A) is weakly unperforated.
  ```

  Unique trace collapses all ordered-`K_0` states to the trace, weak
  unperforation gives strict projection comparison, and real rank zero
  promotes this through hereditary projection approximate units to strict
  comparison of all positive elements.  Uniform Gamma then gives
  Z-stability.  Thus any real-rank-zero counterexample must have perforated
  `K_0`; outside real rank zero the same condition cannot see soft Cuntz
  perforation.
