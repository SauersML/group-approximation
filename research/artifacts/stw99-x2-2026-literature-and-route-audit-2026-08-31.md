---
title: STW X(2) 2026 literature, quantifier, and route audit
---

# Outcome

No unconditional proof or counterexample to STW Problem X(2) was found.
The literature and the Cairn routes still leave the quasidiagonality of the
hyperfinite II1 factor open as of 2026-08-31.  This audit records one sharper
positive cell and corrects two tempting but invalid inferences.

## Primary-source status

* Schafhauser--Tikuisis--White, arXiv:2506.10902, still list X(2) as
  Problem X(2) and call the trace of `R` the likely heart of the nonexact
  quasidiagonality problem.
* Popa, "Q5: Is R quasidiagonal?", W*-News, 2026-05-28, states the problem
  as open and gives the operator-norm Folner and local-AFD formulations used
  in Cairn.
* Alekseev--Thom, arXiv:2606.07369 (2026-06-05), postdates Popa and proves
  Ulam stability of `R` in normalized trace norm on the operator-norm unit
  ball.  Its conclusion and every defect hypothesis are in `||.||_2`; the
  paper neither states quasidiagonality nor supplies operator-norm Folner
  projections.  In particular, its dimension-free matrix stability theorem
  corrects an `L^2`-approximate map to an `L^2`-near homomorphism after
  amplification.  It does not convert normalized Hilbert--Schmidt leakage of
  a finite-rank projection into operator-norm leakage.  The rank-one bad
  direction example therefore survives unchanged.
* Kun--Thom, arXiv:2608.06222, gives new nonsofic generalized wreath
  products of residually finite Kazhdan groups.  Nonsoficity by itself does
  not supply non-MF-ness under the operator-norm definition used by this
  Cairn, and the paper constructs neither a faithful hyperfinite character
  nor an embedding into `U(R)`.  These groups do not currently close the
  negative route.

## The group-shaped quantifiers

There is no contradiction between the established node
`x2-witnesses-are-never-group-shaped` and the live node
`non-mf-subgroup-of-hyperfinite-factor-unitary-group`.

The established theorem excludes only:

1. a reduced group algebra with its canonical character `delta_e`;
2. a topologically amenable reduced crossed product with its
   invariant-measure trace; and
3. a unitary tuple whose restricted trace has `delta_e` joint moments.

The live negative route asks for a non-MF group `Gamma` with a different,
faithful hyperfinite character `chi`, meaning `chi(g) != 1` for `g != e`
and `pi_chi(Gamma)''` injective.  Such a character need not vanish away from
the identity.  Its image `C*(pi_chi(Gamma)) subset R` is a group-generated
C*-algebra, but it is not a canonical-trace reduced group algebra.  Thus the
phrase "group-invisible" in the earlier node must not be read as excluding
this route.  The route remains logically live; the Kazhdan, literal-group,
Clifford-packet, and finite-packet results exclude candidate families, not
all faithful hyperfinite characters.

## Positive-route improvement

The entrywise relative-commutant cut previously required
`dist_2(Y,M_d)=O(d^{-5/2})`.  The nodes
`stw99-x2-local-afd-at-partial-trace-rate` and
`stw99-x2-partial-trace-rate-proof` replace all entry cuts by one cut of

```text
sum_i Tr_matrix(z_i* z_i + z_i z_i*) in M_d' cap R.
```

The positive block inequality

```text
X <= d (1 tensor sum_a X_aa)
```

then proves the local-AFD criterion at the sharper sufficient rate
`O(d^{-1})`.  The column-isometry refuter has size `d^{-1/2}`, so the
black-box relative-commutant gap is narrowed from exponents `[1/2,5/2]` to
`[1/2,1]`.  Hyperfiniteness still supplies no rate, so this does not prove
X(2).  The constant `d` in the positive-block inequality is sharp at the
maximally entangled rank-one block, so the same partial-trace estimate cannot
be iterated or reweighted to improve `d^{-1}`.

## Exact remaining blockers

* Positive: obtain operator-norm Folner projections, or local-AFD witnesses,
  without any dimension/rate hypothesis.
* Negative: construct a non-MF countable group with a faithful noncanonical
  hyperfinite character.  No theorem in this cluster rules out that
  possibility in general.
