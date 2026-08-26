---
rg: 2
id: mf-safe-finite-presentation-compiler
kind: claim
title: Compile the FIN free-factor switch to finite presentations without losing its MF branch
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
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

Generic effective Higman embedding does not solve this.  The completed
compiler uses the three-generator bridge, intersects the ordinary MF-safe
benign witness with the fixed finite-CEP graph witness for `B3(1)`, and
tensors the graph factor's finite swap models with the regular-MF model of
the whole first rope group.  The negative branch is preserved because the
recursive bridge embeds; the positive rope is regularly operator-MF.

## Attempts

The doubles/amenable-edge refactor formerly stopped at asymmetric HNN
identification.  `regular-mf-tensor-sync-proves-twisted-rope-mf` and
`graph-witness-product-supplies-tensor-sync` close that edge without changing
its Britton compression semantics.
