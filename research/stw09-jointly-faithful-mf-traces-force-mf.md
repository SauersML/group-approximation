---
rg: 2
id: stw09-jointly-faithful-mf-traces-force-mf
kind: claim
title: Jointly faithful MF traces force an MF algebra
distinct_from:
  faithful-mf-models-realize-all-mf-traces: that theorem assumes the algebra is already MF and selects a prescribed MF trace in faithful coordinates; this theorem derives the MF property from a family of possibly nonfaithful MF traces.
  stw99-problem-x1-amenable-traces-quasidiagonal: that open problem would promote every amenable trace to a quasidiagonal trace; this theorem is unconditional and instead combines point-separating operator-norm MF trace models.
  stw99-problem-vii-blackadar-kirchberg: that asks whether stable finiteness alone forces quasidiagonality for nuclear algebras; this uses the strictly more structured hypothesis that MF traces jointly detect every nonzero element.
artifacts:
  - research/artifacts/stw09-ix1-separating-mf-traces-audit-2026-08-30.md
---

**ESTABLISHED MF-TRACE SEPARATION THEOREM.**  Let `A` be a separable unital
C-star algebra and let `T` be a family of MF tracial states on `A`.  Suppose
that `T` is jointly faithful, in the concrete sense that

```text
for every 0 != a in A there is sigma in T with sigma(a* a) > 0.       (JMF1)
```

Then `A` is MF.  Consequently, if `A` is nuclear, then `A` is
quasidiagonal.

In particular, the conclusion holds whenever `A` has a faithful tracial
state `tau` in the weak-star closed convex hull of its MF tracial states.
Indeed, if every MF trace vanished on `a* a`, weak-star continuity of
evaluation at `a* a` would force `tau(a* a)=0`, contradicting faithfulness.
Thus this gives an unconditional UCT-free positive subclass of STW Problem
IX(1).  Neither the faithful trace itself nor any individual member of `T`
is assumed to be an MF trace with faithful support.

DERIVATION
stw09-finite-direct-sum-mf-separation-proof
