---
rg: 2
id: jacobson-first-root-packet-admits-coherent-relative-correction
kind: claim
title: The full Jacobson first-root packet and boundary packet correct coherently while fixing the original finite group
distinct_from:
  jacobson-boundary-cell-reconstructs-finite-root-packet: that corrects the smaller boundary packet; this additionally corrects the full first-level matrix root packet and aligns both packets on their actual larger intersection.
artifacts:
  - research/artifacts/jacobson-first-root-packet-coherent-rounding-2026-09-08.md
---

Use the exact compatible representations of `F,J` from
`jacobson-boundary-amalgam-gap-characterizes-mark-collapse`, with
`H=pi_J(h)`, and set

```text
w=||W-I||, beta=||(Hb)^3-I||,
epsilon=322w+368beta,
delta=6057epsilon <= 2,228,976(w+beta).
```

Let `P=Mat_(3 x 3)(F_2)_add semidirect F` be the first-level
root packet, and let `I=P intersect J` be its specified literal
intersection of order 2304. Equivalently,

```text
I=N_0 semidirect (P_Q x K_P),
N_0={matrices supported on rows {1,3} and columns {1,3}}.
```

If `delta<=1/100`, there are exact representations `sigma_P,sigma_J`
on the original dimension satisfying

```text
sigma_P|F=pi_F,
sigma_P|I=sigma_J|I,
H'=sigma_J(h), ||H'-H||<=340delta.
```

The common root is exactly `sigma_P(D_1)=H'a_1H'`; the original
head mark and all of `F` stay fixed. The remaining errors satisfy

```text
||(H'b)^3-I|| <= beta+1020delta,
||W(H')-I|| <= w+4080delta.
```

The cross commutations `[r,H'a_iH']=1` become exact, so the TS
defect norm equals the pure tail defect norm
`||[u',H'rH']-r||`, with `u'=[H'cH',k]`.

This statement establishes coherent finite-packet correction. It does
not assert that either remaining relator becomes exact or that its
unrestricted matrix infimum is positive.

DERIVATION
jacobson-first-root-normal-form-and-overlap-polar-proof
