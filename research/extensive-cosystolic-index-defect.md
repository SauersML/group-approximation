---
rg: 2
id: extensive-cosystolic-index-defect
kind: claim
title: A marked presentation forcing positive-density index syndromes to pay HS relator energy
distinct_from:
  relator-only-hs-obstruction-has-trivial-model: That proves the unmarked version is impossible as an existence obstruction because every presentation has the identity tuple; this target explicitly conditions on separation of a nontrivial marked word and asks for a quantitative energy payment.
  index-density-is-amplification-stable: That is the scaling fact saying density is the only additive-index normalization left invariant by tensor amplification; this is the missing construction that must also turn the density into actual relator energy.
  additive-index-instability: That kills raw parity/Fredholm indices under amplification; this asks for Theta(d) local syndromes together with a bounded-overlap energy inequality.
  hs-expander-block-decomposition: That is a decomposition theorem for one specific normalized-HS stability route; this is a presentation-level certificate intended to rule out separated microstates directly.
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

Construct a finite group presentation

```text
P = < S | R >
```

a word `z` which is nontrivial in the presented group, and constants
`alpha,c,C>0` with the following property, uniformly in the matrix dimension
`d`.

For every unitary `S`-tuple `U=(U_s)_(s in S)` satisfying the marked
separation

```text
||z(U)-1||_2 >= alpha,
```

associate a family of local integer/rank **index syndromes**.  Whenever the
relator defect is below a fixed small threshold, require at least `c d`
independent syndrome carriers and, crucially, a bounded-overlap energy
estimate of the form

```text
#(nonzero syndrome carriers) / d
   <= C * sum_(r in R) ||r(U)-1||_2^2.                 (EID)
```

Equivalent variants are allowed: the carriers may have bounded rank rather
than rank one, the right side may use a fixed finite packet of consequences of
`R`, and bounded overlap may replace literal orthogonality.  What is
load-bearing is that the constants are dimension-independent and that the
positive syndrome density **pays normalized-HS relation energy**.

Combining the two displayed requirements gives

```text
sum_(r in R) ||r(U)-1||_2^2 >= c/C
```

for every separated tuple in the small-defect regime, a contradiction.  Thus
no sequence of presentation microstates can simultaneously drive all relators
to zero and keep the nontrivial word `z` separated.

## Why this is the corrected index target

The previous version asked only for positive index density in every
small-relator-defect tuple.  `relator-only-hs-obstruction-has-trivial-model`
exposes the first missing hypothesis: the identity tuple satisfies every
relator exactly, so an existence obstruction must consume separation.  There
was a second logical gap as well: a topological index ordinarily obstructs
**repair to an exact representation**, while hyperlinearity requires only the
existence of approximate representations.  Positive index density by itself
therefore does not contradict hyperlinearity.  Inequality `(EID)` is the
missing conversion from topology to existence.

The intended mechanism remains cosystolic/qLDPC expansion.  A marked word
creates a nonzero global syndrome; expansion should force that syndrome to
occupy `Theta(d)` local carriers, while local testability and bounded overlap
should make those carriers charge disjoint or bounded-multiplicity pieces of
the relator energy.  This is exactly the kind of local-to-global statement
high-dimensional expanders and locally testable codes are built to provide.
The unsolved translation is from code coordinates to invariant/rank data of a
unitary presentation microstate.

## Attempts

**One Bott/Fredholm defect.**  Dead.  Bounded rank has density `O(1/d)` and is
invisible after normalized-HS amplification (`additive-index-instability`).

**Positive density without energy payment.**  Also insufficient.  Almost
commuting matrices can carry nonzero topological index at arbitrarily small
defect; an index can certify non-repairability without certifying
nonexistence.  The route to nonhyperlinearity needs `(EID)` or an equivalent
quantitative payment.

**Relator-only forcing.**  Impossible as stated in the former version: all
generators equal to `1_d` is an exact tuple in every dimension.  The marked
word is now part of the target precisely to remove that degeneracy.

**Coefficient code directly.**  Still open.  Known cosystolic/qLDPC theorems
control the weight of a classical/quantum-code syndrome.  No theorem in this
repository converts a separated unitary word into `Theta(d)` local index
carriers satisfying `(EID)`.  That translation is now the entire construction
problem, rather than an implicit step hidden inside the word "defect".
