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
- **The obstruction already occurs in a finite canonical matrix packet on
  the full marked pair.**
  `two-site-a5-center-has-exact-boundary-countermodel` takes four `A5` lamp
  sites and an involution which moves the marked pair to the disjoint pair
  and back.  In the finite regular representation all group relators,
  canonical mixed word traces, rational center identities, and shared
  conjugation relations hold exactly, but the compressed four-atom coupling
  of the mover and its inverse has total-variation composition defect
  `3815/5184`.  Therefore fixed two-site center data cannot by themselves
  force an equivariant multiplicity table in normalized Hilbert--Schmidt
  norm.  A positive proof must retain boundary/path labels or independently
  extract a coherent actor table; the example does not rule out either
  enlargement.
- **Full word-path memory has a positive interior lemma, but a uniform
  non-Folner boundary.**
  `full-a5-path-memory-kills-holonomy-but-not-reiter-boundary` puts a separate
  transported center PVM and transported atomwise basis over every retained
  actor word.  Every internal arrow is then a literal block permutation, with
  dimension-free normalized-HS control in the approximate case.  With
  arbitrary path multiplicities, however, the largest matched part for a
  generator `s` has mass
  `1-(1/2)||s mu-mu||_1`.  Making all these losses vanish is exactly Reiter
  amenability, impossible for the pinned property-`(T)` actor.  Thus path
  enlargement removes local holonomy but cannot supply the near-total table;
  a genuinely non-path finite chart carrier, with the matrix model closing
  its boundary, is still required.
- **Fixed lamp exactification leaves a quantified partial-commutant
  cocycle.**  `canonical-a5-window-leaves-a-partial-commutant-cocycle`
  exactifies every fixed `A5^Y` window to a regular core and shows that an
  arrow defined on `D subset Y` still carries the full unitary algebra
  `rho(A5^D)'' tensor B(ell^2(A5^(Y minus D)) tensor C^m)`.  Boundary
  completions contribute a permutation holonomy, and actor multiplication
  only turns the residual unitaries into the corresponding twisted cocycle.
  A fixed finite family of extra binary labels leaves a positive-density
  matrix block.  Only a growing actor-normalized copy Cartan forces
  monomiality, but extracting that Cartan is already the missing finite
  action carrier.
- **Exact expander and finite-quotient carriers close the boundary by
  collapsing the mark.**
  `exact-expander-a5-carriers-collapse-marked-center` gives the direct
  Kazhdan estimate.  In every genuine finite `G`-action, an A5 center label
  which is `delta`-invariant under the fixed generators of `Gamma` differs
  from its `h`-translate on at most `4 delta/kappa^2` of the carrier.  The
  canonical marked lamps instead differ on mass `35/72`.  Hence one cannot
  exactify the actor to a finite quotient/expander action first and attach
  the center field afterward.  The actor permutations and lamp labels must
  be extracted simultaneously as a genuinely approximate table; the
  finite-quotient kernel cocycle is the obstruction to doing this by Fell
  untwisting.
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
- **Exactifying the actor on the active corner is already terminal, not a
  classicalization step.**  Suppose a positive-density reducing corner of a
  proposed microstate is replaced by a genuine finite-dimensional actor
  representation `pi`.  For the pinned compressor
  `t Gamma t^(-1)<Gamma`, conjugation gives an inclusion

  ```text
  pi(t) pi(Gamma)' pi(t)^* subset pi(Gamma)'.
  ```

  Both algebras have the same finite vector-space dimension, so the inclusion
  is equality.  This is the commutant form of
  `compression-defect-dies-in-finite-dimensions`.  The source lamp at
  `Gamma` lies in `pi(Gamma)'`; hence its `t`-translate at `tGamma` lies in
  the same commutant and is fixed by every `gamma in Gamma`.  Choosing
  `gamma` which moves `tGamma` collapses the two distinct lamp coordinates,
  contrary to the canonical C2 profile and, after applying the rational
  central idempotent, to the A5 separation mass `35/72`.

  Thus there are two sharply different outputs.  A **genuine exact** actor
  representation on the active corner immediately proves the desired
  contradiction, as formalized by
  `kt-wreath-relative-canonical-actor-exactification`; a useful
  **classicalization** must instead produce genuinely approximate
  permutations and labels simultaneously.  Property `(T)` supplies the
  Kazhdan estimate after one of those carrier structures is present, but is
  not a normalized-HS stability theorem producing either structure.  This
  rules out the intermediate proposal “property `(T)` first exactifies the
  actor, then the finite lamp packet selects a monomial basis.”
