# Hyperbolic residual finiteness and perfect-completeness LCS: integration boundary

Date: 2026-09-20. **Neither main problem is solved by this integration.**
The request to finish and publish does not supply the missing universal
finite-quotient argument or the missing constant-soundness reduction.

## Material being preserved

The supplied inactive peer-session handoff covers the hyperbolic campaigns
and waves two through five. Its proof artifacts, canonical dependency nodes,
source programs, explicit witnesses, completed computation receipts, and
failed-run logs are retained together. The original review descriptions are
provenance from that session, not a claim that every computation has been
rerun in this integration. The targeted replay and graph-validation receipts
identify the new checks separately. No Lean formalization or external referee
certification of this research is claimed.

The strongest concrete finite construction remains the explicit
28-dimensional Lie algebra over F7 in
`experiments/hrf-wave4-four-generator-2026-09-20/class_five_lie_witness.json`.
Its standalone verifier checks the Lie identities, exact nilpotency class,
generation, and all six marked faces. The resulting group has order 7^28
and detects the selected central generator with order seven. Consequently
the selected mod-seven central extension virtually splits; it is not the
proposed invisible-central-element counterexample.

The later GAP runs reach lower exponent-seven central class ten with central
order seven. Class eleven stopped during finalization and has no completed
result. Ordinary nilpotency class and lower exponent-seven central class
must not be conflated. Failed runs and checkpoints do not certify order 49
or its impossibility.

## Additional bounded checks

* `hrf-stability-next-gap-rounding-2026-09-20.md` shows that nearest seventh-root
  rounding can destroy a fixed scalar gap in the actual approximate-model
  setting.
* `hrf-stability-next-single-core-2026-09-20.md` proves the reducing-partition
  mass estimate and strengthens the example: the rounded tuple can be
  irreducible while its gap tends to zero. Extracting an unchanged reducing
  block cannot repair this. A modified doubled core is already supplied by
  Liu's pruning theorem; preservation of the required finite-order relations
  is not supplied by that theorem.
* `notes/lcs-existential-frame-signed-six-sector-2026-09-20.md` contains an
  exact honest extension and an exact cheating model for the tested frame
  construction on every loopfree graph. It is an audit of this construction,
  not a general impossibility theorem for LCS reductions.
* `notes/lcs-existential-frame-approximate-anchor-2026-09-20.md` checks the
  approximate-only escape. Tensor amplification preserves vanishing relation
  errors while producing forbidden-pattern mass 1/9. The positive natural
  isotypic weight 1/640 is retained as a caveat, not mistaken for zero.
* `notes/liu-internality-current-audit-2026-09-20.md` checks the exact source
  scope and selected analytic steps. It does not independently reprove the
  entire analytic theorem.

Two final repair attempts were also checked, without closing either root:

* `notes/hrf-stability-next-iteration-audit-2026-09-20.md` derives a genuine
  contraction of the mean squared edits in the proposed prune/double/round
  iteration, but its certified gap changes as c -> c^2/1024. These estimates
  do not support the needed uniform-gap induction. The note does not claim
  that every possible algorithm has this deterioration.
* `notes/lcs-existential-frame-natural-corner-2026-09-20.md` checks the
  positive-weight-corner repair in the explicit signed-six model. On K4
  the six transported natural-type projections commute and have zero joint
  intersection; their total leakage from any projection P is at least
  tr(P). Thus this particular common-corner decoder also fails.

The independent audit lane reviewed the approximate-anchor, single-core,
natural-corner, and iteration arguments and reported PASS with these limited
scopes. Root also read the calculations. These are written proof reviews,
not formal certificates or claims of historical novelty.

## Fresh verification in this integration

Three standalone exact verifiers were replayed on MSI acn112, using one
CPU with nice level 19 and bounded runtime: the order-7 central detector,
the H31 mod-five rank-2975 certificate, and the three 400-coordinate
PSL2(19) square-cover cycles. All passed. The replay receipt records input
hashes and the exact exported snapshot. Other archived computations retain
their original review/replay provenance; they were not all rerun here.

The canonical parser, linter, dependency compiler, and changed-node duplicate
check are run against a pinned Git tree, with artifact existence checked
against that same tree. This deliberately avoids overwriting the shared
generated frontier. It is not a full CLI build, a Lean build, or a proof
of either main conjecture. Raw GAP output is preserved byte-for-byte,
including its trailing spaces; the source whitespace check excludes only
that whitespace category.

## Still required for a breakthrough

For the geometric target, construct a word-hyperbolic group and prove that
one specified nonidentity element dies in **every** finite quotient, or prove
universal residual finiteness instead. None of the tested quotient families
has been shown to exhaust all finite images.

For the quantum target, give an effective machine-indexed LCS construction
with quantum value one on the halting branch and one uniform soundness gap
on the nonhalting branch. Value one need not be attained in finite dimension.
Neither removing exact models nor a fixed qc/qa separation proves this.

Only the scoped research handoff is included in this integration. Unrelated
concurrent Lean, Boone--Higman, and quantum-PCP work is not swept into its
commit. The shared generated frontier is not overwritten.
