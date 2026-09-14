---
rg: 2
id: weak-mf-groups-can-carry-rigid-defects
kind: claim
title: Operator-norm MF groups can carry nontrivial rigid compression defects
distinct_from:
  weak-mf-does-not-imply-sofic: that separates operator MF from soficity with the symmetric double and a citation of the updated Kun--Thom Theorem A; this exhibits a nontrivial rigid defect in the finite-lamp amalgam, so the defect criterion fails in the operator-norm class, and nonsoficity follows from the Hamming defect criterion rather than from the double theorem.
  corona-commutant-no-growth: that asked whether operator-norm relative commutants of Kazhdan images grow; this is the group-level consequence that the rigid defect survives in faithful corona models of an explicit group.
  symmetric-double-weak-mf: that is the positive operator-norm MF theorem for doubles and finite-lamp amalgams; this adds the defect computation in the finite-lamp amalgam.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** Let `Gamma < G` be the Theorem E pair and `K != 1` finite.
The amalgam

```text
H_K = G *_Gamma (Gamma x K)
```

has two properties:

- it is MF in the operator-norm corona sense (`symmetric-double-weak-mf`);
- its rigid pair `Gamma <= G <= H_K` has a nontrivial defect.

For `k in K \ {1}` (which centralizes `Gamma`), a strict compressor `t`, and
`gamma in Gamma \ t Gamma t^-1`,

```text
[t k t^-1, gamma] != 1 .
```

So the criterion "approximable groups have trivial rigid defect" fails in the
exact operator-norm class, and normalization fails in matrix coronas,
matching `corona-commutant-growth-witness`. By
`sofic-groups-kill-rigid-compression-defects`, every `H_K` is nonsofic.

**Contrast.** The defect does die in the normalized-Hilbert--Schmidt shadow of
every operator-norm model (`kazhdan-asymptotic-commutant-transport`), with
only `Gamma` Kazhdan. Operator norm has an exact rank germ for rounded
Kazhdan projections, but that size controls only the 2-norm; see artifact
Section 10.

Derivation: `weak-mf-groups-can-carry-rigid-defects-proof`.
