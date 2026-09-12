---
rg: 2
id: kun-thom-clifford-covers-are-f3-linear-sofic
kind: claim
title: The Kun--Thom Clifford covers are F_3-linear sofic
distinct_from:
  kun-thom-wreath-linear-sofic: that asks for complex linear soficity of the untwisted wreath W; this asks for F_3-linear soficity of the central covers E_S, which for nondegenerate graphs implies F_3-linear soficity of W.
  kun-thom-clifford-cover-weakly-sofic: that proves the covers weakly sofic by a permanence theorem that forgets the metric; this asks for the rank metric over F_3.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

**OPEN.** For the Kun--Thom Theorem E pair and every `G`-invariant graph `S` on `G/Gamma`, the Clifford
cover `E_S` embeds in a rank-metric ultraproduct `prod_omega GL_(n_k)(F_3) / d_omega`.

Payoff: `E_S` is nonsofic, so this would give `F_3`-linear sofic nonsofic groups, and every `F_3[E_S]` would
be stably finite.

## Attempts

- **Equivalent to rank embeddings.** For nondegenerate `S`, `E_S` is `F_3`-linear sofic iff `A_S` embeds in
  a rank ultraproduct, and then `W` is `F_3`-linear sofic too
  (`clifford-skew-ring-rank-models-give-linear-sofic-wreath`).
- **Tensor spinor models: dead.**
  - Sofic approximations of the site action, implemented on spinor or tensor modules, turn Hamming-small
    permutation defects into rank-large operators.
  - Truncating fermionic Fock space does not help. Clifford truncation needs neighbouring particle-number
    sectors of comparable dimension, so near half filling, while permutation defects on `delta n` sites are
    rank-small only at low filling.
- **Finite quotients: dead.** Every finite quotient of the complete-graph cover kills `eps`
  (`complete-graph-clifford-cover-center-dies-in-finite-quotients`), so models must not factor through
  them.
- **Not excluded by Kun--Thom.** Their centralizer argument rounds near-invariant permutation data of the
  Kazhdan subgroup. No rank-rounding analogue is known over finite fields, so it does not forbid rank
  models with `eps = -1`.
