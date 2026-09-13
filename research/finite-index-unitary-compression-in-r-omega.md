---
rg: 2
id: finite-index-unitary-compression-in-r-omega
kind: claim
title: A unitary of the ultraproduct of the hyperfinite factor strictly enlarges a subalgebra with Jones index 4
distinct_from:
  invariant-size-collapse: that says a conjugation-invariant monotone size forbids strict compression, and that the trace is refinement-blind at infinite index; this is an explicit strict unitary compression at finite index 4, so no Jones-index size exists either.
artifacts:
  - research/artifacts/un-tracial-support-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setup.**
- `R = ⊗_{k∈Z} M_2` is the hyperfinite II₁ factor with the product trace.
- `s` is the shift `k -> k+1`.
- `R^ω` is a tracial ultraproduct, with `R` embedded as constant sequences.

**Statement.** There is a unitary `v ∈ R^ω` with `Ad v|_R = s`. For `A = ⊗_{k>=0} M_2`,

```text
v* A v = ⊗_{k>=-1} M_2 ⊋ A,        [v* A v : A] = 4.
```

**Why it matters.**
- `hyperlinear-groups-kill-rigid-compression-defects` needs the tracial ultraproduct to rule out
  `A ⊊ σ(u)Aσ(u)*` for relative commutants.
- This example shows that no size read off the position of a subalgebra does that, even at finite Jones index.
- So any obstruction must use how `A` arises: as the commutant of a Kazhdan image, with the compressor in a Kazhdan
  group.
- With the locally finite Pauli group on coordinates `k < 0`, it also realizes a nontrivial compression defect in
  a hyperlinear group. That is consistent, since the subgroup has no (T).
