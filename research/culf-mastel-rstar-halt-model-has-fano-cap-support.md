---
rg: 2
id: culf-mastel-rstar-halt-model-has-fano-cap-support
kind: claim
title: The halting Culf--Mastel R-star instance has a perfect CE model with Fano-cap local supports
artifacts:
  - research/artifacts/fano-one-ghost-compiler-audit-2026-08-22.md
distinct_from:
  culf-mastel-rstar-uniform-fano-cap-profile: that compiles all possible cap profiles into one marked LCS; this is now the sole source-specific existence statement needed for that finite compilation.
  rstar-fano-cap-support-preserves-nonru-affine-relaxation: that proves soundness after a cap profile is given; this asks whether the published completeness construction supplies such a profile.
---

OPEN.
Choose a perfect CE model in the halting branch of a realization of the
Culf--Mastel family over `R_*` such that, in every `R_*` context, its positive
joint spectral support becomes a Fano cap after translation by the ghost.

Equivalently, no local support contains all three points of a Fano line.
By `rstar-cap-support-is-one-character-row`, this open assertion is exactly
the following finite representation theorem, called **FC-char** in the
2026-08-22 audit:

```text
for every HALT instance there is a perfect CE representation such that,
for every nonlinear context c, some a_c != 0 satisfies

X_(c,2)^(a_(c,2)) X_(c,3)^(a_(c,3)) X_(c,4)^(a_(c,4)) = -I.    (FCC1)
```

Equivalently, the representation factors through one of the `7^m` explicit
two-row affine LCS profiles.  The character may depend on the representation
and on the context; no computable canonical choice is required because the
finite exact OR compiler enumerates every profile.

This must be checked in the actual perfect-completeness reduction to the
fixed language; NP-hardness of `R_*` alone does not preserve quantum support.
`culf-mastel-rstar-reduction-is-support-blind` verifies that Theorem 6.8
applies to `R_*` but that its stated classical extension map supplies no
no-Fano-line support conclusion.

## Attempts

- Pairwise arc pruning does not force the property: two equality-linked
  copies of the full seven-point relation are already a pruning fixed point.
- Passing to an extreme trace does not force it either; see
  `extreme-traces-and-local-pruning-do-not-select-fano-caps`.
- Minimal-support selection may shrink a particular satisfying face, but no
  theorem currently shows that a support-minimal perfect CE model of the
  Culf--Mastel instance cannot retain a forced Fano line.  This is the exact
  remaining possible canonical operation.
- On the finite-dimensional HALT strategy one may at least choose a
  support-minimal irreducible summand, by
  `finite-perfect-strategy-reduces-only-to-support-minimal-irrep`.  This
  minimizes only among central blocks of that representation; a simple block
  can retain every local atom, so the Fano conclusion still requires the
  source instance's overlap geometry.
- Noncentral postselection cannot improve this central-block reduction.
  `tracial-cap-menus-are-central-core-partitions` proves that every normal
  tracial convex decomposition of one supplied model into cap-supported
  branches is exactly a partition by central profile carriers.  It also
  proves that a noncentral compression is neither an exact representation
  nor a tracial branch, and its dilation firewall shows that adjoining a
  central selector or a multiplicity-commutant ancilla cannot improve the
  situation while preserving the supplied trace.  Hence a factor model with
  one full-support context admits no model-selective cap menu at all; a
  positive construction must find a different perfect trace or build a
  genuinely new representation/compiler.
- A constraintwise cap-range refinement of the classical NP reduction cannot
  solve the problem on a full nonaffine source support:
  `fano-cap-range-sections-cannot-encode-nonaffine-relations` would then turn
  the pp-gadget into an affine definition of that source relation.  Thus a
  positive result must use a proper support selected by the perfect trace or
  genuinely global contextual correlations.
- **The actual-support obstruction is now exact.**
  `fano-cap-witness-sections-force-source-affine-safety` traces the reverse
  homomorphism in Corollary 6.7 and proves that cap-supported witnesses for
  the positive source atoms force
  `Aff(S_i) subseteq C_i` in every source context.  A full-support
  one-in-three context fails because its affine hull adds `111`.  Constant
  answer size makes this condition finitely enumerable but does not imply it.
  The remaining positive possibility is therefore source-specific: prove
  that the particular HALT perfect strategy used before the NP reduction has
  affine-safe support in every answer and accepted-pair context.
- `dfnqxy-answer-reduction-does-not-preserve-affine-safe-support` audits the
  preceding Hadamard answer reduction.  All of its equality and code/subset
  tests are affine-safe; only the PCPP `Verify` views remain.  A three-outcome
  perfect EPR strategy gives an explicit counterexample showing that the
  transformation does not preserve affine safety in general.  Thus the
  cited perfectness/oracularizability argument cannot close this node: one
  must inspect the particular HALT strategy's positive PCPP view images.
- The alternative Lemma-20 source in
  `cmps-two-oracular-rstar-lift-has-commuting-context-stars` closes the
  mutual-neighbor hypothesis: its `2`-oracularizable completeness strategy
  survives a fixed-language `R_*` lift with jointly commuting incident
  context algebras.  This enables joint pruning, but does not itself exclude
  a full seven-point support or prove the affine-safety condition above.
- The tempting universal empty-link strengthening is false for that actual
  lift.  `star-surjective-nonaffine-context-blocks-fano-empty-link-lift`
  applies to a copied proper 3SAT clause: every one of its seven satisfying
  assignments extends through the whole CMPS star, and private-auxiliary
  `R_*` lifting preserves those extensions.  If every descended occurrence
  hit every Fano line by an empty link, the witness ranges would all be caps;
  affinizing and projecting them would make the seven-point source relation
  affine, a contradiction.  Radius-two commutation therefore supplies the
  operator step of joint pruning but cannot supply its required line-hitting
  combinatorics here.
- `rstar-cap-support-is-one-character-row` proves that cap support is exactly
  one fixed nonzero character identity per context and exactly factorization
  through one of the `7^m` affine LCS profiles.  This makes the downstream
  compiler smaller and turns the present node into `(FCC1)`, but does not
  select one character in the HALT model.  Likewise
  `fano-maximal-cap-overlap-has-positive-sequential-mass` gives a profile of
  squared sequential mass at least `(4/7)^m`; such a product need not be a
  common reducing corner, so the central-core firewall still applies.
- The fiberwise auxiliary selector is valid only under a stronger syntax;
  its unconditional one-context core is
  `isolated-rstar-context-determinizes-to-a-fano-cap`, and its simultaneous
  private-tail form is `rstar-private-tail-fiberwise-cap-collapse`.  The
  displayed common
  annihilator gives the homogeneous row `lambda dot t=0`, whose three
  nonzero solutions form a Fano line and whose operator sign is `+I`, not
  FC-char's `-I`.  The local argument is repaired because the replacement
  support has at most two points, so another functional takes value one on
  both.  The global application nevertheless fails:
  `culf-mastel-rstar-has-no-private-tail-form` proves that the published hard
  family cannot have three occurrence-private auxiliary coordinates in every
  target row.  Corollary 6.7 makes auxiliaries private between source
  gadgets, not between the `R_*` occurrences inside one gadget.
- The selector does extend well beyond globally private tails.
  `rstar-two-retained-coordinates-admit-a-fixed-cap-section` proves that any
  row can be cap-completed while retaining an arbitrary set of at most two
  coordinates.  Reversing the deletion order in
  `rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel` therefore makes
  every row outside a computable incidence kernel cap-supported.  Every row
  left in that kernel has at least three pinned-or-internally-shared
  coordinates.  This is a genuine narrowing, but the paper does not choose
  concrete pp gadgets whose kernels could be enumerated; see
  `culf-mastel-rstar-two-tail-core-is-not-specified`.  Moreover every exact
  gadget for a nonaffine source relation necessarily has a nonempty pinned
  kernel.  Thus leaf peeling cannot by itself close FC-char; the remaining
  theorem is a finite cap-profile compatibility result on a chosen dense
  gadget core, together with source-specific control of the positive support.
- `rstar-core-character-profiles-induce-an-exact-affine-cover` states that
  compatibility result precisely for any fixed gadget.  Its `k` core rows
  induce an effectively enumerable cover of the source relation by at most
  `7^k` affine subrelations `A_beta`.  A positive source support admits a
  cap-valued witness section exactly when it is contained in one `A_beta`.
  The published reduction neither fixes this cover nor proves that the HALT
  support selects one of its pieces.  This is the sharpened conservative
  frontier after leaf elimination.
- Mere source affine safety cannot close that frontier.
  `source-affine-safety-does-not-imply-rstar-profile-compatibility` gives an
  explicit three-row pp gadget whose visible relation is all of `F_2^3` and
  an affine four-point support whose witnesses force a Fano line in one
  target row.  The positive proof must therefore choose and audit concrete
  pp gadgets jointly with the actual HALT support; the hull condition alone
  is insufficient.
- There is an exact local alternative rather than an intermediate case.
  By `fano-unsafe-support-compresses-to-a-full-nand-packet`, any context that
  is not cap-supported contains, on the sum of three line atoms, two parities
  with full support `F_2^2 minus {00}`.  This identifies the nonlinear mass
  but does not globalize it: the line projection is not a reducing carrier,
  and a purely Boolean unary-binary tracial instance is classical.
- The exact long-code version has a smaller bad-sector ledger than arbitrary
  cap failure suggests.  By
  `rstar-odd-character-ghost-fiber-is-eight-sectors`, 56 of the 64 marked odd
  characters already xor-decode to an allowed `R_*` point; only the seven
  Fano-line characters and the full-set character decode to the ghost.  Their
  conditional canonical mass is exactly `1/8`.  This does not prove FC-char:
  the eight-sector ghost projection has positive regular trace and is not a
  common reducing carrier across contexts.  It does, however, localize any
  matrix-specific long-code or packet attack to those eight sectors.
