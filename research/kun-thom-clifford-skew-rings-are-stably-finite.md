---
rg: 2
id: kun-thom-clifford-skew-rings-are-stably-finite
kind: claim
title: Every anti-central Clifford skew ring of the Kun--Thom pair is stably finite over F_3
refuted_by: [clifford-cover-anti-half-skew-ring-not-directly-finite]
distinct_from:
  oriented-kun-thom-clifford-skew-rings-are-stably-finite: that covers graphs with an invariant finite out-degree orientation, through the matrix-lamp wreath; this covers every invariant graph, the complete graph included, and is the full negation of the counterexample target.
  kun-thom-wreath-stably-finite: that is the untwisted factor F_3[W], already established; this is the anti-central factor, where every landed method fails.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

**OPEN.** Let `Gamma < G` be the Kun--Thom Theorem E pair, and `X = G/Gamma`. For every `G`-invariant graph
`S` on `X` and invariant `q`, the Clifford skew ring `A_S` over `F_3` is stably finite.

Equivalently, since `F_3[W]` is stably finite, every `F_3[E_S]` is stably finite, and no Kun--Thom Clifford
cover carries a linear Gottschalk counterexample over `F_3`.

## Attempts

- **Marked sites: dead.** `kun-thom-clifford-skew-rings-sf-via-marked-sites` is invalidated by
  `nondegenerate-clifford-skew-rings-have-no-finite-dim-reps`. A nondegenerate `A_S` has no unital map into
  any group algebra or marked-site ring.
- **Rank models: gated.** Route `kun-thom-clifford-skew-rings-sf-from-f3-linear-soficity` needs every `E_S`
  to be `F_3`-linear sofic. For nondegenerate `S` that is equivalent to a rank embedding of `A_S`, and it
  implies `F_3`-linear soficity of the Kun--Thom wreath
  (`clifford-skew-ring-rank-models-give-linear-sofic-wreath`).
- **Oriented graphs.** All of them sit in one algebra, the matrix-lamp wreath, so
  `oriented-kun-thom-clifford-skew-rings-are-stably-finite` needs only
  `matrix-lamp-wreath-algebras-are-stably-finite`. The complete graph is not covered there.
  - Pairwise anticommuting finitely supported elements with a common infinite Delta-system would have to
    anticommute through a finite kernel algebra.
  - No equivariant local realization is known.
- **Filters any witness must pass.**
  - **Nonsofic support.** Its support generates `H <= G` with `Vtilde_S semidirect H` nonsofic, so `H` is
    nonamenable (Clifford cover artifact, Section 4.1).
  - **Trace.** Its defect has `F_3`-trace `0`.
  - **Oriented graphs.** It already appears in the complete-graph skew ring over `X x 3`
    (`oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath`).
