---
rg: 2
id: tracial-bcs-rationalizes-full-overlap-distributions
kind: claim
title: A tracial BCS has rational context weights matching every full overlap distribution
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas: that matches the two ranks of each shared binary variable; this simultaneously matches every joint sign pattern on every entire context intersection.
  near-perfect-bcs-strategy-gives-synchronous-relator-state: that transfers approximate strategies to approximate states with a modulus; this is an exact finite rational-polytope statement.
---

Let `B` be a finite BCS with a tracial state.  There are rational numbers
`mu_(c,a)>=0`, `a in R_c`, summing to one in each context, such that for every
two contexts `c,d`, every intersection

```text
S=U_c intersect U_d,
```

and every sign pattern `sigma in {+1,-1}^S`,

```text
sum_(a in R_c:a|_S=sigma) mu_(c,a)
 =sum_(b in R_d:b|_S=sigma) mu_(d,b).                    (RFO1)
```

After clearing one denominator, all weights become integer coordinate
multiplicities of a common total dimension `D`.  Equation `(RFO1)` then gives
a coordinate bijection between the two context models which intertwines
**all** shared signs simultaneously.

The rational weights are computable by finite rational linear programming.
They need not have full support; zero-weight allowed assignments may be
discarded.  No global finite-dimensional BCS representation is asserted,
because the separately chosen overlap bijections can have nontrivial cycle
holonomy.
