---
rg: 2
id: two-site-a5-center-classicalization
kind: claim
title: Canonical A5 lamp microstates classicalize the marked two-site center field
distinct_from:
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that extracts coherent charts for every finite site window and proves the whole coordinate action sofic; this asks only for the marked pair and only for the rational two-valued A5 center field.
  two-point-orbit-approximation: that is the resulting finite permutation statement about the bare G-set and is refuted for the Kun--Thom pair; this asks whether canonical microstates of the A5 lamp wreath would force that statement.
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that starts after one exact finite actor table acts on a common PVM; this must extract an approximately multiplicative finite actor table from arbitrary microstates.
---

Let `Gamma<G`, `X=G/Gamma`, and `(p,q)=(Gamma,hGamma)` be the pinned
Kun--Thom marked pair.  Put

```text
W_5=A5^(X) semidirect G.
```

Prove that every canonical-trace normalized-Hilbert--Schmidt microstate
sequence for `W_5` yields the finite permutation states and labels required
by `two-point-orbit-approximation` at `(p,q)`.

The input label field is fixed and quantitative.  Apply
`two-site-a5-plancherel-center-separates-mark` to the two coordinate lamps.
The rational five-dimensional central type gives two projections whose
exclusive-or mass tends to `35/72`, and every actor incidence which keeps a
slot inside `{p,q}` transports the corresponding projection with vanishing
normalized-HS error.

The remaining assertion is an **equivariant two-site multiplicity
classicalization**.  For every finite actor window, replace the actor
unitaries by permutations on a finite state carrier so that

1. their normalized Hamming multiplication defects tend to zero;
2. on a density bounded below independently of the window, the two center
   labels are distinct; and
3. every pair-preserving actor incidence transports those labels literally.

Standard shrinking then makes the distinct-label set have the density
required in the two-point definition (or the construction may amplify the
fixed `35/72` carrier before shrinking).

This is strictly weaker than invariant Cartan completion or recovery of the
whole action.  Only two rational packet projections are retained.  It still
cannot follow from scalar actor traces or one-normalizer covariance: the
actor may carry an arbitrary unitary cocycle in the packet multiplicity
fiber.  A proof must use joint actor multiplication and the cylinder-resolved
mixed canonical traces to permutationize that cocycle on the separated
two-site carrier.

## Attempts

- **Diagonalize the four two-site center atoms and round each actor.**  This
  works only for actor elements which preserve the marked two-site packet.
  A general element in the multiplicativity window transports its two lamp
  coordinates to a different packet, so it need not normalize the four-atom
  algebra.  Arbitrary completions of those partial atom maps need not
  multiply.
- **Apply the finite-cylinder mixed-trace theorem.**  Once a finite group
  acts exactly on one common atom PVM,
  `finite-cylinder-mixed-traces-kill-normalizer-holonomy` removes every
  multiplicity gauge.  Producing that common finite actor table is exactly
  the missing step; applying the theorem beforehand is circular.
- **Tensor with a residual finite quotient of the actor and Fell-untwist.**
  Local actor twists disappear on lifted Cayley balls, but a global section
  leaves a cocycle in the finite-index kernel, as computed in
  `finite-quotient-fell-untwisting-leaves-kernel-cocycle`.  That cocycle may
  act arbitrarily on the two-site multiplicity fibers.
- **Use squared block norms as classical transition kernels.**  Relative to
  the four center atoms, every actor unitary gives a bistochastic coupling,
  and Birkhoff decomposes each coupling into permutations.  Separate
  decompositions do not preserve actor multiplication: inserting the atom
  PVM between two unitaries destroys off-diagonal interference.  A live
  positive approach would prove that the canonical mixed cylinder moments
  make this interference negligible on the `35/72` exclusive-or carrier,
  or charge the failure to the actor relator energy.  No such joint coupling
  estimate is presently established.
- **The fixed-PVM coupling route is now refuted exactly.**
  `bernoulli-center-measurement-retains-boundary-interference` computes the
  canonical one-site coupling of a mover and its inverse.  Sequential
  measurement forgets the moved label and leaves total-variation defect
  `35/72` even at zero presentation defect.  Hence a positive construction
  must retain path/boundary memory in its finite state space; it cannot form
  actor products by composing conditional kernels on one fixed lamp window.
- **Positive physical rank is not an adjoint amplifier.**  The exclusive-or
  carrier has trace `35/72`, so left multiplication by it is a projection of
  adjoint rank `35/72`.  Its range is only invariant under a stabilizer which
  preserves the carrier.  It is not pointwise fixed.  More strongly,
  `canonical-infinite-subgroup-has-zero-adjoint-fixed-density` shows that the
  pointwise-fixed part for the infinite Kun--Thom stabilizer has adjoint
  density zero in every canonical microstate.  Hence the packet data cannot
  feed `macroscopic-child-only-adjoint-sector-is-terminal` without a genuinely
  new multiplicity-charging operation.  Rephrasing the physical projection
  as a superoperator does not supply that operation.
