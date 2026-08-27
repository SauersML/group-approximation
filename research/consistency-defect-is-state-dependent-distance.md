---
rg: 2
id: consistency-defect-is-state-dependent-distance
kind: claim
title: Outcome disagreement and Hilbert-Schmidt distance are the same number
distinct_from:
  markov-sofic-equals-sofic: that identifies two model classes; this is a metric identity inside one finite model, and says nothing about which models exist.
  traffic-branching-rounding-hierarchy: that asks a rounding question about branching observables at finite defect; this supplies the metric such a rounding argument would be stated in, and is proved outright.
artifacts:
  - GroupApproximation/Sofic/ConsistencyDistance.lean
---

Let `Y` be a finite model with normalized trace `tau`, let `alpha` be a finite
outcome set, and let `A,B : alpha -> M_Y(C)` be two families with

```text
sum_a A_a = 1,   sum_a B_a = 1.
```

Define the **state-dependent squared distance** and the **consistency defect**

```text
d(A,B)     = sum_a ||A_a - B_a||^2,                        (CD1)
cons(A,B)  = Re tau(A_tot B_tot^H) - sum_a Re tau(A_a B_a^H),   (CD2)
```

where `||X||^2 = tau(X X^H)` is the normalized Hilbert-Schmidt norm.  Then

```text
d(A,B) = 2 cons(A,B)      if every A_a and every B_a is a projection,  (CD3)
d(A,B) <= 2 cons(A,B)     if every A_a and every B_a is an effect,     (CD4)
```

where an effect is a matrix `E` with `0 <= E` and `0 <= 1 - E` in the positive
semidefinite order.

The two quantities answer different questions.  `cons` is what a **test**
measures: it is the average mass the pair places on *disagreeing* outcomes, and
it is the quantity a hypothesis about a near-representation hands you.  `d` is
what a **rounding argument** needs: it is what "these two measurements are
interchangeable" means quantitatively, and it composes along a chain by
`d(A,C) <= 2 d(A,B) + 2 d(B,C)`.  `(CD3)`/`(CD4)` say that the observable
quantity and the structural one are the same quantity.

Neither statement needs `card(Y) > 0`: both sides are computed from the same
`tau(1)`, so the degenerate model cancels instead of having to be excluded.

**Classical instance.**  For `f : Y -> alpha` let `P^f_a = diagonal 1_{f = a}`
be the readout measurement of `f`.  Then

```text
cons(P^f, P^g) = |{y : f y != g y}| / |Y|,                            (CD5)
```

the normalized Hamming distance.  So `(CD3)` reads: the Hilbert-Schmidt
distance between two classical readouts is twice their Hamming distance, and
`(CD4)` is the statement that a quantum measurement pair obeys the same law.
That is why the identity belongs to this programme rather than to quantum
information alone: the metric a near-action is measured in and the metric a
rounding argument produces are the same metric, so a rounding hierarchy may be
stated in either and read in the other.

**Credit.**  The two quantities and the identity between them are the
statement-level design of Section 4 of Ji, Natarajan, Vidick, Wright and Yuen,
*Quantum soundness of the classical low individual degree test*
(arXiv:2009.12982), the technical core of MIP* = RE, where consistency and
state-dependent distance are the two numbers the whole soundness argument is
carried in.  A Lean formalization of that development exists as
`LionSR/MIPStarRE`, the source of the Palomar registry entry
PALOMAR-2026-08-18-000001; that repository carries no licence, so nothing is
copied from it.  The setting here is deliberately different: the state is the
normalized trace of a finite model rather than a vector state on a bipartite
space, which is what makes `(CD5)` -- and hence the whole calculus -- land on
the microstates this development is already about.

**What it does not do.**  It is a change of coordinates, not an input.  It
converts a consistency hypothesis into a distance hypothesis and back, with no
loss beyond the factor of two, and supplies the triangle rule a chain of
rounding steps consumes.  It does not produce a projective family from an
almost-projective one, which is the actual content of any rounding theorem, and
it does not by itself say anything about which finite models exist.
