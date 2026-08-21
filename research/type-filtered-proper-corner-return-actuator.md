---
rg: 2
id: type-filtered-proper-corner-return-actuator
kind: claim
title: Build a wandering proper-corner return on every forbidden marked type
distinct_from:
  finite-matrix-only-exhaustive-marked-type-actuator: that states the general finite-dimensional exhaustive interface; this gives the strongest surviving concrete moment implementation.
  central-marked-swap-star-has-two-word-trace-floor: that assumes one central marked swap star; this filters separately by every primitive marked type and by the context rejection projection.
  single-triangle-trace-cyclic-return-cell: that targets one native Fanizza incidence chord; this targets all types of one fixed context packet and lets finite duality remove alignment.
  one-filtered-wandering-return-is-already-nonhyperlinearity: that proves any one nonzero instance of this interface is already a terminal contradiction, so exhaustive construction is stronger than necessary.
---

**OPEN.**  For each marked type `lambda` of each fixed context packet, put

```text
P_(c,lambda)=q_(c,lambda)F_c.
```

Construct one ordinary wandering return word `r_(c,lambda)` such that:

1. every group-basis support word `g r_(c,lambda)` occurring in
   `P_(c,lambda)r_(c,lambda)` is nonidentity;
2. every finite-dimensional sufficiently accurate canonical microstate has

   ```text
   Re tr(P_(c,lambda) r_(c,lambda))
    >=c_(c,lambda) tr(P_(c,lambda))-omega(delta)       (TFP1)
   ```

   for a positive dimension-independent constant;
3. the perfect commuting model extends exactly and keeps the central mark
   nontrivial.  On its allowed support `P_(c,lambda)=0`, so no proper return
   is demanded there.

A concrete realization may use two partial swaps with common initial
projection `P_(c,lambda)` and orthogonal ranges.  A fixed power of their
product returns the initial carrier in finite matrices, while the product
word remains wandering in the abstract group.  Equivalently one may decode
two block maps whose cyclic products differ by `P_(c,lambda)`.

If `(TFP1)` is proved, `type-filtered-wandering-moments-sum-rejection-mass`
and the fixed game gap remove the whole marked source.  No selected-type
alignment theorem remains.

In fact `one-filtered-wandering-return-is-already-nonhyperlinearity` shows
that the stated target is stronger than this paragraph suggests.  Whenever
`P_(c,lambda)!=0`, clauses 1--2 alone already prove the output group
nonhyperlinear: the canonical trace of the positive finite-packet projection
is nonzero, whereas the filtered wandering moment is zero.  Thus one should
search for **one** nonzero filtered actuator, not build the full finite menu
first.

## Why this survives the induction firewall

The induced representation of a rejected `H`-type is infinite-dimensional
and has no canonical normalized matrix trace.  Clause 2 is not an operator
identity there.  Thus the exact induced representation may contain the
rejected selector character without contradicting `(TFP1)`, while finite
canonical microstates still pay its full normalized mass.

## Attempts

- **Use the SMC predicate commutator itself as `r`.**  Inner covariance makes
  it a finite-packet word after the multiplicity factor cancels; its Fourier
  expansion contains an identity collision and canonical trace does not
  vanish.
- **Impose the return as an exact operator identity on every representation.**
  This is forbidden by induced-representation compression.  The return must
  be decoded only from finite matrix rank/trace geometry.
- **Use one selected primitive type.**  Orthogonal context rotations can put
  the common source outside that type.  The finite family over all marked
  types is essential.
- **Use a finite graph of finite groups.**  Stationary multiplicity flow
  realizes the return in finite dimensions; an infinite-order proper-corner
  actuator or another finite-rank asymmetry is required.
- **Use a residually finite Bass--Serre extension.**
  `residually-finite-models-refute-filtered-wandering-return` constructs an
  exact finite quotient, canonical on any prescribed finite window, in which
  the filtered moment is zero and the filter has its full positive regular
  trace.  This rules out the proposed inequality itself, not only one proof
  strategy.
- **Use a co-dense nonamenable HNN edge.**  This is the surviving HNN form.
  `projective-transfer-gives-universal-filtered-actuator` proves
  that the open projective `SL_3` transfer modulus, followed by one free
  phase-cancelling commutator, gives one word satisfying `(TFP1)` for every
  packet filter simultaneously.  The remaining gap is precisely the robust
  projective commutant transfer, which is already a terminal
  nonhyperlinearity interface.
