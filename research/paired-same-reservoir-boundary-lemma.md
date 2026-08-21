---
rg: 2
id: paired-same-reservoir-boundary-lemma
kind: claim
title: Paired Leavitt children either remain in one multiplicity reservoir or pay their full boundary mass
artifacts:
  - research/artifacts/affine-leavitt-normalized-hs-decoder-audit-2026-08-21.md
distinct_from:
  same-orbit-closure: that asks only for asymptotic square closure on positive paired mass; this is the fixed-depth quantitative leakage alternative needed to prove the affine boundary estimate.
  mixed-relations-force-holonomy-or-transverse-recovery: that asks for a holonomy/transverse-recovery dichotomy on one Pauli overlap; this asks for a boundary ledger through the actual rank-five affine-Leavitt root triangles.
  closed-multiplicity-cycle-kills-carrier-trace: that proves the trace endpoint after the reservoir has returned; this must identify that reservoir or charge the mass that escapes it.
---

OPEN.  Fix a depth `N` in the affine-Leavitt Steinberg presentation.  On the
positive-mass paired long-root sectors recovered from canonical-trace
normalized-HS microstates, decompose each of the first `N` binary branch
steps so that, up to a fixed-depth constant times the named relator and trace
separation error, every unit of parent mass satisfies one of:

1. its two Leavitt children and their two return maps act on the same
   source-sized paired label space and the same multiplicity reservoir; or
2. the unit leaves that reservoir and the leaked normalized mass is charged
   by a paired Steinberg multiplication-triangle defect.

The constants may depend arbitrarily on `N`, but not on matrix dimension or
on the recovered label cardinalities.  The estimate must explicitly exclude
`rectangular-escape`: increasing the child Weyl-label factor while shrinking
its multiplicity is not a closed branch and must enter the leakage term.

Once branch (1) holds, no further near-bijection theorem is needed:
`bistochastic-diagonal-return-forces-aligned-permutation` rounds the square
forward/return pair, and the robust paired `1/36` floor charges the crossed
zero relation.  If the same reservoir closes only after several binary
steps, `closed-multiplicity-cycle-kills-carrier-trace` sums the whole return
with coefficient exactly `3`, independent of depth.  Thus the mathematical
content of this claim is solely the matrix-coordinate identification of the
same finite multiplicity reservoir, or an HS-visible payment for leaving it.

A potentially weaker sufficient form uses transverse descendants instead of
label cardinalities: the mixed rank-five words must recover one and the same
fixed-density projection in both trace-independent child algebras.  Then
`tensor-independent-child-carrier-gap` supplies an immediate dimension-free
energy floor.  Producing unrelated carriers on the two sides is insufficient.

For the specific exact Pauli atlas there is an even weaker, non-generic
alternative.  Its two *distinct* canonical quarter carriers already have D8
holonomy `1/2`.  Therefore it is enough to recover the first in one child
algebra and the second in the commuting transverse child algebra;
`separate-d8-carriers-cannot-recover-in-commuting-descendants` then gives a
fixed floor.  Arbitrary unrelated carriers remain insufficient—the point is
that these two carriers and their joint canonical moments are fixed in
advance by the packet.

Pure tracial-von-Neumann reasoning cannot prove this statement, because the
left regular representation sees the nontrivial marked word.  The proof must
use finite matrix coordinates: multiplicity, finite-label recovery, or an
equivalent microstate feature that is unavailable in an arbitrary finite
tracial representation.

## Attempts

- **Whole-map extraction fails.**  Exact deterministic equivariant maps into
  `V direct_sum V` satisfy every four pairing identity while shrinking
  multiplicity; this is `rectangular-escape`.
- **Equal ambient dimension fails.**  The larger target Weyl factor uses the
  same matrix dimension by consuming the source multiplicity, so a dimension
  count alone sees no loss.
- **Live attack.**  Use the mixed rank-five raw/comb words to identify one
  common returned carrier.  Either their holonomy is nontrivial and pays a
  relator defect, or the carrier lies near both transverse child algebras and
  `tensor-independent-child-carrier-gap` pays a fixed amount.  Extracting the
  word-defined **same** carrier, rather than two unrelated carriers with the
  same trace, is the deferred step.
