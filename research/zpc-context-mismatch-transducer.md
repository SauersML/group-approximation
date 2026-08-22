---
rg: 2
id: zpc-context-mismatch-transducer
kind: claim
title: ZPC predication contexts can charge cross-context mismatch to LCS loss
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-selector-robust-lcs-compiler: that is the full quantitative compiler theorem; this isolates the remaining context-consistency inequality after priority decoding has removed selector overlap from the problem.
---

For the fixed finite tailored game `G` supplied by
`perfect-zpc-irs-quantum-gap-game`, construct a finite binary LCS together with
a finite family of **local predication contexts** `c` (for example edge
contexts) such that perfect ZPC-IRS strategies compile perfectly and the
following quantitative statement holds.

From every finite-dimensional output strategy of loss `epsilon`, extract in
each context commuting selector involutions `Z_(c,a)` and predicated branch
copies `G_(c,a,i)`.  Write

```text
W_c = product_a Z_(c,a),
E_c = (1-W_c)/2.
```

Apply [[odd-selector-priority-decoding]] inside `E_c` and then
[[onehot-predicated-direct-sum-decoder]].  Let `D_pred` be the weighted total
squared defect of the compiled predicated branch equations and let `D_glue`
be a weighted squared mismatch between the resulting decoded copies of every
unreadable question observable occurring in two incident contexts.

There is a constant `C`, independent of matrix dimension, such that

```text
sum_c (1/4)||W_c+1||_2^2 + D_pred + D_glue
  <= C epsilon.                                         (CTX')
```

The mismatch may be measured after the canonical corner identifications used
by the construction; only a dimension-free spanning-tree gluing estimate is
required downstream.

## What has been removed

No pairwise selector-overlap term occurs in `(CTX')`.  Raw selectors may have
large or even maximal overlap.  Odd parity guarantees that every joint atom
has at least one active branch, and priority decoding assigns it to one such
branch without losing mass.  The affine and finite-group selector barriers
therefore do not block this target: the output relations need not prune the
additional odd selector characters.

## Attempts

- **Parity and predicated equations are already linear.**  One parity row per
  context controls the first term, and
  `controlled-linear-predication-normal-form` supplies the branch equations.
- **Only context consistency remains.**  Choose one reference context per
  question and add bounded-degree equality/covariance checks along a spanning
  tree of its incident contexts.  The target is an `L^2` Poincare-style bound
  from those local test losses to `D_glue`, with constants depending only on
  the fixed finite source game.
- **Raw equality and aggregation do not expose the decoded copy.**
  `priority-decoded-contexts-are-not-glued-by-raw-gate-equality` gives exact
  countermodels: branchwise equality of every raw gate across two contexts can
  coexist with maximal decoded mismatch when the selector allocations differ,
  and `product_a G_(c,a,i)` need not equal the priority-decoded observable on
  a multi-active odd sector.  The missing check must therefore be
  selector-payload coupled; ordinary equality rows on the unconditioned gates
  are insufficient.
- **A commuting parity-only coupling is pp-impossible.**
  `selector-gated-equality-is-not-affine-pp-definable` shows that the scalar
  relation “if this selector is active, these payloads agree” is not the
  projection of any affine parity system.  It also gives three canonical
  singleton priority configurations whose ternary XOR has mismatched decoded
  outputs.  Thus arbitrary hidden LCS parity bits cannot implement the
  missing coupling while preserving the full singleton menu.  This does not
  rule out a genuinely projective central-sign gadget with no relevant scalar
  sector, which is now the precise remaining algebraic escape.
- **Odd-XOR aggregation has a scalar ternary-closure obstruction.**
  `affine-nested-odd-xor-selectors-force-affine-behavior` shows that replacing
  the priority decoder by the product of all active payloads does make the
  aggregate independent of a refinement, but only at the price of closing
  the source's accepted scalar behaviors under `x+y+z`.  Finite affine nested
  selectors, vertex-star refinements, and duplicate master labels do not
  alter this: their visible activation set is still affine and therefore
  contains every three-label activation once it contains the singletons.
  Thus the repair works only for source contexts whose accepted-behavior union
  is already affine, or after introducing genuinely selector--payload-coupled
  noncommutative relations.  For aggregation of the **full** answer this is a
  complete dichotomy: `tailored-gap-is-lcs-or-has-a-nonaffine-edge` shows that
  if every full edge relation is affine, the tailored gap was already the
  desired LCS gap.  Projecting to unreadable behaviors can conceal the
  nonaffinity, but then the aggregate has not reconstructed a compatible
  readable answer.
- **The remaining analytic estimate is elementary once labels align.**
  `priority-decoder-lipschitz-under-selector-gate-alignment` proves that the
  identity-completed decoded copies are dimension-free Lipschitz in the
  squared selector mismatch plus squared raw-gate mismatch, with an explicit
  constant depending only on the number of local labels.  Thus the genuinely
  missing construction is a completeness-preserving LCS mechanism producing
  *matched selector allocations* across the verifier's differently labelled
  overlapping contexts; no further matrix-dimensional estimate is hidden
  after that mechanism.
- **Do not globalize readable bits unnecessarily.**  The source ZPC hypotheses
  provide local commutation, not one global readable algebra.  The transducer
  should glue decoded unreadable observables across contexts rather than
  assume all remote selectors commute.
