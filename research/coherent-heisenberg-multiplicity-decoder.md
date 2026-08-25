---
rg: 2
id: coherent-heisenberg-multiplicity-decoder
kind: claim
title: Realize positive-density finite Heisenberg multiplicities on one Leavitt module
---

OPEN.  Let a normalized-Hilbert--Schmidt microstate sequence for the binary
Leavitt elementary group keep one fixed nonzero root a positive distance from
the identity.  Its finite additive and three-root Heisenberg windows determine
compatible multiplicity-density vectors by
`hs-finite-heisenberg-windows-have-compatible-density-measures`.

Construct coordinate projections of uniformly positive normalized trace and
four contractions on the corresponding corners satisfying the two inverse
relations and the binary sum relation of the Leavitt family, with
corner-normalized Hilbert--Schmidt defect tending to zero.

The finite windows already encode addition and multiplication.  The missing
assertion is that their compatible density data have one common
positive-density carrier on which all four coefficient operators coexist.

## Attempts

- **Take the inverse limit of the density vectors.**  This gives a measure on
  the inverse-limit type space, but not coordinate projections carrying four
  compatible matrices.  Positive root mass can drift through finer types so
  that every proposed nested coordinate carrier has vanishing trace.
- **Diagonalize the finite-group exactifications.**  Exactifications for
  different windows can require different small corrections and conjugating
  isometries.  Their scalar branching vectors agree while their matrix
  corners need not be nested or retain a positive common intersection.
- **Use the active root spectral projection.**  Its trace is positive when
  the root survives, but coefficient roots generally move it.  Compression
  back to that projection produces boundary errors not controlled by the
  finite-window multiplicities.
- **Use conditional expectations onto the finite-window algebras.**  The
  resulting martingale produces a limiting tracial sector, but the terminal
  Leavitt trace-floor theorem needs four contractions on actual matrix
  corners with uniformly positive relative dimension.

The remaining theorem is a positive-density gluing result, not another trace
inequality: compatible finite Heisenberg branching data must yield nested
coordinate carriers and coherent Leavitt operators.

`finite-tags-do-not-atomize-heisenberg-schrodinger-tower` makes the remaining
quantifier sharper.  There is an explicit coherent Schrödinger tower in
which the marked central carrier has trace one and all finite Heisenberg
branching identities hold exactly, while each level-`N` polarized coordinate
atom has trace `p^(-N)`.  Tensoring any fixed finite tag packet, including an
`S3` selector, leaves that decay unchanged.  Therefore the decoder cannot
select a bounded menu of fine types and cannot be repaired by a fixed tag.
Indeed a carrier of trace `alpha` requires at least `alpha p^N` level-`N`
characters.  It must aggregate this exponentially wide family while
controlling the coefficient maps between its members, or obtain a genuinely
growing/matrix-only return from additional presentation relations.  The
common central-root carrier itself is already literal; the missing object is
the coherent polarized aggregation inside it.

Nor is reuse of the branch implementers on all windows enough by itself.
`orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates` constructs
one coherent marked microstate sequence for the complete two-branch
Heisenberg HNN skeleton: both child copies commute and generate the parent,
the same two stable letters implement every fixed-depth covariance table,
and all transverse shears are present.  Finite coordinate permutations absorb
the injections at a boundary escaping to infinity.  The missing relation must
therefore come from the coefficient-return part of the full elementary group,
not from more finite Heisenberg self-copy consistency.

Literal synchronization of all occurrences inside that positive-root
coefficient-return language is still insufficient.
`finite-positive-root-fragments-have-marked-regular-models` proves that every
finite collection of positive elementary roots in the actual Leavitt
coefficient ring generates a finite unitriangular `p`-group.  Its regular
representation satisfies all positive-root addition, Heisenberg
multiplication, shared-occurrence, and range-sum-fold identities exactly while
keeping any chosen nonzero root at normalized-HS distance `sqrt(2)` and on a
nontrivial spectral carrier of trace `(p-1)/p`.  Thus the independent tensor
factor in the earlier fold countermodel is not the real loophole.  The
load-bearing payment relation must leave the positive unipotent radical—for
example through an opposite-root, Weyl/Whitehead, or global return row.

The full-presentation check identifies the exact surviving gate.  The
Leavitt identities already give the two orthogonal branch embeddings and the
exponential prefix Heisenberg packet, all reproduced by the calibration
above.  What the coordinate-permutation models avoid is a **same-object
return**: label dimension grows from the source Weyl factor to the two-child
factor while spectator multiplicity shrinks, and no relation returns both to
one physical multiplicity reservoir.  On a reservoir already identified,
`same-reservoir-weyl-pair-has-fixed-depth-doubling-gap` supplies the required
dimension-free defect floor.  In the current affine normalized-HS route, the
precise missing finite-matrix theorem is
`paired-same-reservoir-boundary-lemma`: either authenticate that common
reservoir or charge all mass leaving it to the paired Steinberg triangle
defects.  Proving such a return/payment theorem, rather than strengthening
the scalar Heisenberg densities, is the remaining gate.
