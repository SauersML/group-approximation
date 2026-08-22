---
rg: 2
id: unbounded-noncentral-hecke-corner-wordizes-a2-average
kind: claim
title: An unbounded-depth noncentral Hecke corner wordizes the A2 two-path average
distinct_from:
  no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace: That rules out every finite arithmetic packet at the required rank; this asks for the first genuinely infinite or matrix-coordinate replacement.
  fixed-spherical-polynomials-have-no-42nd-projection: That rules out a fixed continuous spherical polynomial projection; this permits a Borel or moving-depth projection but additionally requires noncentral two-path interference.
  single-denominator-borel-cuts-have-a-rohlin-escape: That constructs moving Borel cuts with the right trace and vanishing one-shift covariance; this requires the cut to participate in the native A2 Gram cross term rather than remain an independent abelian conductor selector.
---

OPEN.  Construct, in canonical arithmetic-double matrix microstates, a
projection `q_n` and a bounded native corner word `Y_n` such that

```text
tau(q_n)->1/42,
q_n is asymptotically D-covariant,
q_n Y_n q_n -> (A_n+B_n)/2,                            (UNC1)
```

where `A_n,B_n` are the two native A2 section transports with relative
holonomy `x_23(2)`.  The construction must also charge the complementary
Julia leakage to the established first-exit ledger.

By `no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace`, `q_n`
cannot come from any fixed finite `K<D`.  By
`fixed-spherical-polynomials-have-no-42nd-projection`, it cannot be one
fixed spherical polynomial.  The smallest surviving source is therefore a
Borel/unbounded-conductor projection, or an equivalent matrix-coordinate
cut whose depth tends to infinity.  It must be noncentral relative to a
second authenticated chart; otherwise
`central-hecke-controlled-multipaths-remain-sectorwise` removes the cross
term in `(UNC1)`.

This is a formulation, not an existence claim.  Its load-bearing content is
the simultaneous combination of moving-depth rank authentication,
`D`-section covariance, and noncentral two-path interference on one carrier.

The most literal finite-congruence implementation is now ruled out.
`parahoric-covariant-congruence-packets-pay-one-over-eighty-four`
shows that every packet inside the left group algebra of the level-`2^n`
image of `D` becomes central under exact section covariance (and uniformly
close to central under approximate covariance).  If it retains trace-zero
`x_23(2)` holonomy, its global Julia leakage tends to `1/84`; if leakage
vanishes, the holonomy is erased.  Thus the source sought here must live in
a genuinely larger relative-commutant/matrix-coordinate algebra, not merely
in a moving finite Borel character packet.
