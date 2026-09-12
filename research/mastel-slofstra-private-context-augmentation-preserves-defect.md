---
rg: 2
id: mastel-slofstra-private-context-augmentation-preserves-defect
kind: claim
title: Private context augmentation preserves weighted BCS defect without globalizing commutation
artifacts:
  - research/artifacts/slofstra-papers-focused-audit-2026-08-20.md
distinct_from:
  finite-selector-gadget-induction-barrier: that forbids deleting nonlinear selector characters inside one finite group; this keeps the original context overlaps and adds private local variables at the BCS-algebra level.
  zpc-selector-robust-lcs-compiler: that seeks a complete quantitative lowering to an LCS; this imports one exact soundness-preserving transformation used inside such a lowering.
---

Let `B` be a BCS with contexts `V_i`.  Enlarge each context to `W_i` by adding
private variables, with

```text
W_i intersect W_j = V_i intersect V_j,
```

and suppose restriction from the satisfying assignments on `W_i` onto those
on `V_i` is surjective.  Then the old and new weighted BCS algebras admit
classical homomorphisms in both directions with soundness constant one.
Consequently a tracial state of defect at most `epsilon` pulls back in either
direction with defect still at most `epsilon`.

This is Mastel--Slofstra, *Two prover perfect zero knowledge for MIPstar*,
arXiv:2404.00926v2, Lemma 6.6 and Corollary 6.7.  Their Theorem 7.5 further
shows that bounded context subdivision pulls near-perfect traces back with a
polynomial defect loss.

For the Schur--Clifford program, the important point is structural: packet
generators may be private to one BCS context.  Their local commutation with
that context's selectors does not imply commutation between unrelated source
contexts.  This validates the contextual placement of finite rank gates at
the BCS level; it does not yet turn those local algebra relations into scalar
group relators.
