---
rg: 2
id: stw08-finite-group-crossed-products-preserve-af-embeddability
kind: claim
title: Finite-group crossed products preserve AF-embeddability
distinct_from:
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: that asks whether exactness and quasidiagonality create an AF embedding; this theorem starts with an AF embedding and transports it across every finite-group action.
  stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable: that asks a UCT-free existence question from one quasidiagonal trace; the traced part here preserves an AF embedding which already extends the trace.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Let `A` be a C*-algebra, let a finite group `F` act on `A`, and suppose that
`A` embeds into an AF algebra `E`.  Then the full (equivalently, reduced)
crossed product is AF-embeddable; more precisely, there is an embedding

```text
A rtimes F -> M_|F|(E).
```

This construction also preserves specified traces.  If `eta:A->E` is an AF
embedding, `sigma` is a trace on `E`, and `tau=sigma eta` is invariant under
the action, then the normalized matrix trace tensored with `sigma` restricts
along the displayed embedding to the canonical crossed-product trace
`tau E_A`, where `E_A:A rtimes F->A` is the coefficient expectation.

Consequently:

- `C_0(X) rtimes F` is AF-embeddable for every finite-group action on a
  second-countable locally compact Hausdorff space `X`;
- if `Lambda` has finite index in a countable amenable group `Gamma` and
  `C*(Lambda)` is AF-embeddable, then `C*(Gamma)` is AF-embeddable, without
  any normality or splitting hypothesis on `Lambda`.
