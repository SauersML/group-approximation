---
rg: 2
id: cmps-rstar-lift-has-line-hitting-empty-links
kind: claim
title: The two-oracular R-star lift hits every Fano line by an empty neighborhood link
refuted_by: star-surjective-nonaffine-context-blocks-fano-empty-link-lift
distinct_from:
  cmps-two-oracular-rstar-lift-has-commuting-context-stars: that supplies the joint neighborhood PVM needed to use empty-link pruning; it does not make any neighborhood link empty.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that is the resulting operator-support conclusion; this is the finite incidence certificate that would imply it for the chosen CMPS lift.
  fano-pruning-is-line-hitting-empty-link: that proves the abstract sufficient condition; this asks whether the concrete fixed-language hard family satisfies it.
---

**REFUTED.**  The former target was: for the fixed-language `R_*` family and chosen perfect completeness
model constructed in
`cmps-two-oracular-rstar-lift-has-commuting-context-stars`, prove that every
target context `c` and every translated Fano line `L` in its seven honest
assignments contain some `a in L` with

```text
Link(c,a)=empty.
```

Here `Link(c,a)` consists of jointly overlap-consistent assignments to all
contexts in one incident variable star, as defined in
`fano-pruning-is-line-hitting-empty-link`.  The radius-two commutation theorem
ensures that these neighboring context PVMs have a joint refinement, but it
does not establish this combinatorial emptiness.

The certificate is finite for every compiled instance: seven line-hitting
obligations per `R_*` context.  It must be proved for the actual CMPS/CM
reduction geometry, not inferred from 2-oracularizability alone.

`distance-two-oracularity-does-not-force-fano-pruning` gives a classical
full-support counterexample to the generic implication, so any proof here
must use additional structure of the hard instances or modify the reduction
while preserving its perfect-gap orientation.

## Attempts

- The direct argument from radius-two commutation fails: the repeated-clause
  classical model has globally commuting algebras and nevertheless gives a
  compatible neighborhood tuple for every honest atom.
- Applying the standard contextwise pp reduction with arbitrary witness
  sections also fails generically.  On a full nonaffine source support,
  cap-valued occurrence ranges would contradict
  `fano-cap-witness-sections-force-source-affine-safety`.
- Fresh-private sunflower checks are combinatorially powerless by
  `rstar-sunflower-neighborhoods-have-full-links`: full one- and
  two-coordinate projections let every center atom extend independently.
  The CMPS equality construction is not entirely a sunflower, however.  Its
  two implication clauses jointly enforce equality between each global
  variable and a local copy.  Those paired clauses are the first concrete
  place where an external star can actually make a neighborhood link empty.
- The remaining attack is source-specific: inspect the CMPS hard-instance
  incidence geometry and its selected completeness model for forced empty
  links--in particular, audit the paired implication/equality blocks--or
  design a non-contextwise reduction with shared auxiliary state (or
  effective three-coordinate overlaps) while retaining the perfect strategy
  and constant NO gap.

The source-specific inspection now refutes the target.  A copied original
3SAT clause in CMPS Lemma 20 is star-surjective: every one of its seven local
satisfying assignments extends through the duplicate and equality-clause
neighborhood.  After the contextwise Culf--Mastel pp lift, any section of
these seven assignments therefore lands inside the nonempty-link set of
every target occurrence.  If every Fano line were hit by an empty link, all
of those occurrence ranges would be Fano caps, contradicting
`fano-cap-range-sections-cannot-encode-nonaffine-relations` for the
nonaffine seven-point 3SAT relation.  See
`star-surjective-nonaffine-context-blocks-fano-empty-link-lift`.
