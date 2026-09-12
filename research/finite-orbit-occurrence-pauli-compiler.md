---
rg: 2
id: finite-orbit-occurrence-pauli-compiler
kind: claim
title: Compile unbounded robust Pauli games through finitely many occurrence-test orbits
distinct_from:
  thompson-clifford-central-product-tape: that globally names exact Pauli cells and then must compare their alternative addresses; this names local test occurrences and makes consistency itself a bounded-arity test orbit.
  finitely-presented-uniform-area-clifford-tape: that asks for the complete multiplication table of every Pauli group with bounded area; this asks only for a robust game's sampled local test relations.
  hs-pcp-boone-compiler: that compiles a machine-indexed verifier with a uniform semantic decoder; this may use one bespoke robust Pauli game family and needs only a dimension witness.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

OPEN.  Construct one finitely presented group with a nontrivial central
involution `J`, a family of finite robust dimension-witness games `G_N`, and
word representatives for every local test occurrence such that:

1. every involution, commutation, anticommutation, linearity/code, and
   occurrence-consistency check belongs to one of finitely many bounded-arity
   orbits under the addressing group;
2. every instance of a check is a literal conjugate of its prototype relator,
   so a tuple of relator defect `epsilon` yields `(OGC2)` with constants
   independent of `N` and address length;
3. the game soundness theorem turns value above one fixed threshold into a
   local dimension lower bound `D_N->infinity`;
4. the exact crossed-product/infinite-tensor model satisfies all relators and
   keeps `J` nontrivial.

The essential change from global naming is that two occurrences of the same
logical observable need not first be proved equal as matrices.  Their direct
consistency test is part of the game and itself has bounded orbit type.  The
linear-code incidence part is now closed by
`finitely-presented-oligomorphic-linear-pauli-addresser`: after adjoining the
finitary linear group, bounded vector/covector configurations have finitely
many orbits classified by relation kernels and pairing matrices.  The open
problem is narrower: prove dimension-independent HS consistency between the
different orbit representatives of one occurrence.  This is not supplied by
high transitivity itself.  The theorem
`two-transitive-occurrence-sections-have-unbounded-pair-holonomy` proves that
for any two global role sections, simultaneous transport of all ordered pairs
has unbounded endpoint stabilizer correction.  A controlled swap placed in
the pair test retains the same two corrections when its endpoints are
identified with the strategy's fixed question operators.  The amenable
Houghton version of the addresser is an exact hyperlinear countermodel to
every proof which omits this quantitative gauge step.

## Attempts

- **Global Thompson names.**  Exact Pauli cells exist, but comparing two names
  of one cell along a stabilizer word pays unbounded length and coherent small
  rotations realize the loss.
- **Linear oligomorphic repair.**  Acting first by the finitary linear group
  makes all bounded linearity and symplectic-pairing predicates finite orbit
  types, and the resulting semidirect Pauli tower is finitely presented.  This
  solves the incidence enumeration, but not the normalized-HS section/gauge
  coherence between different representatives.  Choosing an amenable
  addresser makes the whole exact construction hyperlinear and proves that
  this remaining distinction is load-bearing.
- **Pairwise controlled swaps.**  Every pair test may be a literal conjugate
  of one prototype, but a game strategy still needs one fixed operator for
  each question.  Comparing the simultaneously transported endpoints with
  those fixed question words inserts two unbounded stabilizer holonomies by
  `two-transitive-occurrence-sections-have-unbounded-pair-holonomy`.
- **Direct complete-table tests.**  These fall back to
  `finitely-presented-uniform-area-clifford-tape`, which is stronger than the
  occurrence target and retains the table-area obstruction.

## 2026-08-21 bounded-neighbor audit

Moving from a two-transitive pair orbit to bounded-neighbor incidence avoids
the specific global-section theorem, but it does not yet produce a compiler.
Two new exact fences isolate what the bounded-neighbor architecture must do.

- `bounded-neighbor-pauli-needs-growing-equality-components` gives
  a constant-dimensional exact Pauli model for every bounded-degree graph of
  pairwise commute/anticommute tests.  Therefore sparse Pauli edges alone
  cannot certify dimensions tending to infinity.  A viable degree-reduced
  Pauli game must retain growing equality/linearity components (normally
  robustified by expanders), or use genuinely higher-arity structure.
- `ascending-hnn-expander-levels-do-not-have-fixed-prototype-edges` audits the
  natural finite-index Kazhdan tower.  Its levels `K/phi^n(K)` really are
  finite expanders, and their stabilizer relations really are conjugates of
  base relations.  But their fixed generating-set edges are not: translating
  a prototype edge to depth `n` turns its step into `phi^n(s)`, which fixes
  the level root, while translating the genuine edge back produces the
  scale-dependent word `t^-n s t^n`.  Simultaneous conjugacy cannot change
  the orbit index from `1` to `[K:phi^n(K)]`.
- `regular-tree-consistency-has-vanishing-spectral-gap` shows that switching
  to unique tree addresses removes holonomy at the price of an `O(1/N)`
  agreement gap: one centroid edge separates two macroscopic operator
  assignments.  And `regular-cayley-prototype-components-have-fixed-size`
  shows that a fixed finite menu of translated equality offsets has cosets of
  one fixed subgroup as its complete components, so those finite components
  cannot grow.

Thus the surviving bounded-neighbor target is narrower: construct a finite
scale-conversion cell for the expander consistency edges, or a finitely
presented incidence system whose growing equality components are already
literal finite-template components.  Merely replacing the dense orbit by a
Cayley/Schreier expander does not remove the quantitative word problem.

There is, however, a real positive geometric source for the second option.
`fp-cayley-expanders-give-bounded-occurrence-edges`, using the
Sapir--Osajda constructions, gives a finitely presented group whose Cayley
graph contains a finite expander family with every edge difference in one
fixed finite word ball.  Actual group elements name the vertices, so all
consistency checks are literal conjugates and no section is used.  What is
still missing is not expander naming: it is a globally satisfiable placement
of the complete degree-reduced Pauli pair/linearity incidence system on those
words, with many logical equality classes rather than one subgroup orbit.

That statement is now formalized exactly.  Expander-cloud replacement is
dimension-preserving by
`expander-cloud-reduction-preserves-pauli-dimension-gap`.  Given a typed
Cayley placement with distinct row and column cosets and disjoint sign double
cosets, `relative-coset-pauli-incidence-compiler` constructs the finite group
presentation and an explicit infinite Clifford model keeping `J!=1`.
The remaining placement theorem is
`colored-cayley-pauli-incidence-separation`; its load-bearing content is the
relative coset/double-coset separation `(CCP1)`, not bounded edge length.

## 2026-08-22 private-matching update

The new private Weyl sampler changes the placement problem decisively.  Its
mixed X--Z occurrence graph is a matching, not a degree-reduced copy of a
dense logical rectangle system.  By
`private-matching-free-product-separates-pauli-signs`, pair `t` can be placed
at `(s^t,s^t p_b)` in `F(s,p_0,p_1)`.  All pair relations are literal
conjugates of two sign prototypes, free normal form separates the signs, and
no endpoint is compared with a second mixed occurrence.  Thus neither pair
holonomy nor colored relative small cancellation is a remaining gate for
this branch.  The exact model is the invariant coset-Heisenberg
representation, so the marked central sign survives.

The matrix-valued dimension witness is already uniform for exact additive
actions by `private-random-weyl-sampler-forces-growing-matrix-dimension`, and
the finite samples are recursively selectable by
`private-weyl-samplers-admit-recursive-selection`.  What is still missing is
not mixed-pair consistency or sign-double-coset separation.  It is the
same-basis compiler: bounded-template relations must turn all privately
named X occurrences (and separately all Z occurrences) into one exact
additive action with dimension-independent normalized-HS loss and at most a
fixed dimension-enlargement factor.  This is
precisely `same-basis-rounding-interface-for-sparse-weyl-sampler`.
