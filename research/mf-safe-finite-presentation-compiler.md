---
rg: 2
id: mf-safe-finite-presentation-compiler
kind: claim
title: Compile the FIN free-factor switch to finite presentations without losing its MF branch
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
  - research/artifacts/regular-mf-tensor-sync-shulman-completion-2026-08-26.md
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
distinct_from:
  threshold-free-reverse-kleene-mf-higman: that compiler preserves a marked radical/nontriviality dichotomy and yields one non-MF group; this must preserve an actual MF positive branch across every input.
  monotone-mf-switch-positive-branch-barrier: that rules out one append-on-halt marked architecture; this asks for a nonmonotone or MF-safe finite-presentation envelope.
  symmetric-double-weak-mf: that proves one MF-safe group operation; this needs a complete effective compiler assembled from such operations.
---

**ESTABLISHED.**  There is a total computable map `e |-> P_e` into finite
presentation codes
such that

```text
W_e infinite  => Carrier(P_e) is MF,
W_e finite    => E embeds in Carrier(P_e),
```

for one fixed finitely presented non-MF group `E`.

The completed compiler applies effective Higman embedding only to obtain a
finite presentation and marked embedding words, then tests its kernel with a
Mikhailova fiber-product subgroup inside a direct product of free groups.  The
ambient benign witness is therefore residually finite on every branch. Its
product with the fixed graph witness inside `F_2 times F_2` supplies the exact
kernel and the finite swap models; tensor synchronization finishes the rope.
The negative branch is preserved because the recursive bridge embeds, and the
positive rope is regularly operator-MF.

The analytic endpoint is literature-relative but unconditional: tensor
synchronization constructs faithful edge-compatible corona embeddings, Ueda
identifies the universal HNN algebra as a corner, and Shulman's
arXiv:2603.13564v2, body Theorem 16 makes the ambient amalgam MF. The left-regular
representation then proves that the abstract HNN group embeds in that MF
algebra. The reusable statement is
[[twisted-hnn-mf-permanence-with-corona-conjugator]].

## Attempts

The earlier doubles/amenable-edge proposal never constructed a complete
MF-safe pre-rope witness.  The Mikhailova construction supplies that missing
object directly; `regular-mf-tensor-sync-proves-twisted-rope-mf` and
`graph-witness-product-supplies-tensor-sync` close the remaining final edge
without changing its Britton compression semantics.
