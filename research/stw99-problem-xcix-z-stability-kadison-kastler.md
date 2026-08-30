---
rg: 2
id: stw99-problem-xcix-z-stability-kadison-kastler
kind: claim
title: Z-stability is uniformly open for the Kadison--Kastler metric (STW Problem XCIX)
root: true
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
---

**Problem XCIX of Schafhauser--Tikuisis--White.**  Does there exist a
universal `epsilon > 0` such that, whenever `A,B` are C*-subalgebras of the
same `B(H)`, `A` is separable and Z-stable, and

```text
d(A,B) < epsilon,
```

then `B` is Z-stable?

The general problem remains open after a literature check through 2026-08-30.
The nuclear subclass is settled with the explicit radius `1/420000` by
`stw99-xcix-nuclear-radius-positive`.  In fact the same radius applies when
the *nearby target* `B`, rather than `A`, is separable and nuclear; see
`stw99-xcix-either-side-nuclear-radius`.  Without nuclearity on either side,
the strongest uniform conclusion recorded here is scaled-Cu agreement at
radius `1/6422957`, not Z-absorption.

## Attempts

The similarity route is quantitative: Z-stability gives property `D_(5/2)`,
which turns Kadison--Kastler closeness into complete closeness.  At the
audited radius `1/6422957`, this yields an isomorphism of scaled Cuntz
semigroups by `stw99-xcix-scaled-cu-radius`.  Consequently any counterexample
inside this ball must cross the genuine gap between having the invariants of
a Z-stable algebra and absorbing Z; it cannot be detected by scaled Cu.

The central-copy route also stalls quantitatively.  A finite-set embedding of
Z can be transported across a near inclusion, but the resulting commutator
bound incurs the additive loss `304 sqrt(gamma) + 2 gamma` from
`stw99-xcix-central-copy-transfer-bound`.  Alternating this raw transport does
not improve the estimate: after `n` legs the certified loss is `n` times this
quantity, and the two commutator Lipschitz constants used in the estimate are
sharp for arbitrary contraction perturbations; see
`stw99-xcix-raw-transport-iteration`.  This is a rigorous obstruction to that
specific black-box iteration, not an obstruction to selecting better copies
using the strongly self-absorbing structure.  Z-stability requires
arbitrarily small centrality errors while `gamma` is fixed, and no such
uniform structural error-improvement principle is known.

There is nevertheless a sharp asymptotic rigidity statement.  If a sequence
of unital common-unit pairs has distance tending to zero and the first
coordinates are Z-stable, the two norm ultraproducts are literally equal and
the common ultraproduct is Z-saturated: every separable subset has a commuting
unital copy of Z.  Quantitatively,
`stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance` shows that
every fixed finite centrality defect of the nearby coordinates tends to zero,
uniformly over the chosen contractions.  Thus a counterexample sequence must
escape to increasing witness complexity or decreasing tolerance even though
its limit has exact relative-commutant copies.  This isolates a failure of
uniform coordinate reflection, not an invariant defect of the limit algebra.

Finally, Z-stability is closed, rather than known open, in the space of
separable unital subalgebras of one fixed ambient algebra containing a common
unit; see `stw99-xcix-z-stability-is-kk-closed`.  This only rules out one fixed
`B` being a Kadison--Kastler limit of Z-stable `A_n` in that space.  It does
not rule out varying counterexample pairs `(A_n,B_n)` with
`d(A_n,B_n) -> 0`, which is exactly what failure of a universal radius could
produce.
