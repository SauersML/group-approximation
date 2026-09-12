---
rg: 2
id: harris-lp-to-llp-implication-is-one-directional
kind: claim
title: Only one direction of the Harris three-dimensional criterion is available, and the recorded converse is unsupported
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  llp-failure-has-three-dimensional-hyperrigid-witness: that records the Harris construction and its negative normal form; this is the correction to one paragraph of it, isolating which implication the sources supply and which was asserted without a valid derivation.
  lp-of-harris-generator-system-forces-nonhyperlinear: that consumes `LP(S_A)` to force non-hyperlinearity and is unaffected; this concerns only the reverse implication that node used to assert as well.
  harris-lp-is-maximal-matrix-range-collapse: that gives a numerical matrix-range criterion for proving `LP(S_A)`; this decides nothing numerically and only fixes the logical strength of the target that criterion aims at.
---

**ESTABLISHED (correction, 2026-08-23).**  For Harris's explicit
three-dimensional hyperrigid system `S_A=span{I,D,G} subset M_(n+2)(A)` built
from `n` unitary generators of a unital C-star algebra `A`:

```text
LP(S_A)  =>  LLP(A)                     is available;        (H1D1)
LLP(A)   =>  LP(S_A)                    is NOT.              (H1D2)
```

`(H1D1)` is Harris Proposition 3.4(2) followed by matrix and corner
permanence of the LLP; equivalently, Corollary 3.5 is its contrapositive.
`(H1D2)` was recorded in this graph with the justification "ambient LLP
restricts to the lifting property on every finite-dimensional operator
subsystem".  **That justification is invalid**, and no replacement is
available from the cited sources.

Proof of invalidity: `harris-lp-to-llp-one-directional-proof`.

**The gap in one sentence.**  LLP of `A` is a statement about ucp maps whose
domain is `A` (equivalently `M_k(A)`): it says such a map into a quotient lifts
after restriction to a finite-dimensional operator subsystem.  LP of `S_A` is a
statement about ucp maps whose domain is `S_A`, and an arbitrary ucp map out of
a finite-dimensional operator subsystem need not be the restriction of any ucp
map on the ambient algebra.  Hyperrigidity does not repair this: it constrains
ucp maps on `C^*(S_A)` that agree with a *representation* on `S_A`, not ucp
maps out of `S_A` into an arbitrary quotient.

**Reported but not relied on.**  A 2026-08-23 dossier reports that Harris,
arXiv:2607.11001v1, explicitly remarks that the converse to Proposition 3.4(2)
fails even under hyperrigidity.  The primary PDFs are not in this tree and were
not re-read on that date, so that remark is carried here as an attributed
report only; nothing above depends on it.  Confirming it at source would
upgrade `(H1D2)` from "unsupported" to "false", which is a strictly stronger
statement than what this node asserts.

**Cascade effect: none.  Priority effect: real.**  Every route in this graph
that consumes the Harris system uses `(H1D1)` only --
`nonhyperlinear-from-three-dimensional-hyperrigid-lp`,
`km-harris-maximal-matrix-range-collapse`,
`harris-lp-is-maximal-matrix-range-collapse`,
`explicit-prs-harris-three-dimensional-system-has-lp` -- so no derivation is
withdrawn and no target changes status.  What changes is how the Harris target
should be ranked: `LP(S_A)` is a *sufficient* condition for the LLP family and
is potentially strictly stronger than it, so the three-dimensional normal form
is a smaller *statement* but not a smaller *problem*, and it should not be
preferred over the ambient LLP targets on the ground that it is the same
question in fewer dimensions.  It remains a legitimate and fully explicit
sufficient route.
