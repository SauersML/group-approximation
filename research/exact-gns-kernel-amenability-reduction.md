---
rg: 2
id: exact-gns-kernel-amenability-reduction
kind: claim
title: Exact algebras reduce amenable-trace quasidiagonality to the faithful GNS image
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: this is a reduction from an arbitrary trace to a faithful trace under exactness, not a proof that the faithful trace is QD.
  amenable-trace-descends-through-locally-liftable-quotient: that is a general quotient descent lemma assuming local liftability; this verifies that hypothesis for the GNS quotient of an exact algebra and adds the QD pullback step.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `A` be an exact unital C*-algebra, let `tau` be a trace, put
`J=ker(pi_tau)`, and let `bar_tau` be the induced faithful trace on `A/J`.
Then

```text
tau is amenable on A  iff  bar_tau is amenable on A/J. (1)
```

For every `A`, without exactness, quasidiagonality of `bar_tau` implies
quasidiagonality of `tau=bar_tau o q`.  Consequently, a positive solution for
faithful amenable traces on exact algebras implies a positive solution for all
amenable traces on exact algebras.

No converse QD descent from `tau` to `bar_tau` is asserted.
