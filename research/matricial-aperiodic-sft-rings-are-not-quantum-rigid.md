---
rg: 2
id: matricial-aperiodic-sft-rings-are-not-quantum-rigid
kind: claim
title: An exactly matricial crossed product of an aperiodic Z^2 SFT carries periodic quantum tilings at every scale, so the shift is not quantum rigid and the algebra is not finitely presented
distinct_from:
  periodic-quantum-tilings-refute-quantum-rigidity: that derives noncommutation and non-rigidity FROM a periodic quantum tiling; this produces the tilings from an exact matricial embedding of the crossed product and chains the two
  exactly-matricial-rings-have-lef-general-linear-groups: that gives LEF groups from an exact matricial embedding of any ring; this gives quantum tilings from an exact matricial embedding of an SFT crossed product
artifacts:
  - research/artifacts/un-converse-subshift-models-2026-09-13-part2.md
---

**ESTABLISHED** (route `matricial-aperiodic-sft-rings-are-not-quantum-rigid-proof`; artifact §§1–2). Unreviewed.

Let `Ω ⊆ A^(Z^2)` be an SFT with no periodic point, `k` a field, and `R_Ω = LC(Ω,k) ⋊ Z^2`. Suppose `R_Ω` embeds
unitally in an algebraic ultraproduct of matrix algebras over fields. Then:
1. for every `D >= 1` there is a periodic quantum tiling of `Ω` at scale `D` (axioms (Q1)–(Q3) of
   `sft-crossed-product-fp-iff-quantum-rigid`) on a finite-dimensional space over a finite field;
2. `Ω` is not `D`-quantum rigid for any `D`, and `R_Ω` is not finitely presented.

**Contrapositive.** If `R_Ω` is finitely presented and `Ω` is free and minimal, then `R_Ω` is a simple, finitely
generated, stably finite ring that is not exactly matricial. Its elementary groups (simple mod centre, Kazhdan, linear
sofic by `free-minimal-subshift-elementary-groups-are-simple-kazhdan`) then decide between
`stably-finite-simple-rings-have-mf-elementary-groups` and `stably-mf-elementary-groups-force-matricial-rings`.

The new step is item 1. One Łoś coordinate of the embedding is pushed into a matrix algebra over a finite field, where
the translation matrices have finite order. That supplies the period lattice, and the window identities give
(Q1)–(Q3).
