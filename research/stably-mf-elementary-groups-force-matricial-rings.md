---
rg: 2
id: stably-mf-elementary-groups-force-matricial-rings
kind: claim
title: If every elementary group over a simple ring is MF (or LEF), is the ring exactly matricial, or does it at least carry a Sylvester rank function?
distinct_from:
  exactly-matricial-rings-have-lef-general-linear-groups: that is the proved direction, exact matricial embeddability giving LEF; this asks for its converse
  el3-rank-models-factor-through-ring-rank-models: that is the rank-metric analogue for one rank and characteristic p, asking that rank models of EL_3 factor through ring rank models; this asks for the operator-norm (MF) and LEF analogue in stable rank
  stably-finite-simple-rings-have-mf-elementary-groups: that asks whether the weakest ring condition suffices; this asks whether the strongest one is necessary
---

**OPEN.** Let `R` be a countable simple unital ring such that `EL_N(R)` is MF for every `N`. Does `R` embed
unitally in an algebraic ultraproduct `∏_ω M_(d_k)(F_k)` of matrix algebras over fields? Weaker forms:
- does `R` carry a Sylvester matrix rank function?
- does the same follow when `EL_N(R)` is LEF for every `N`?

A positive answer, together with `exactly-matricial-rings-have-lef-general-linear-groups` and
`mf-elementary-groups-force-stably-finite-simple-rings`, makes the ring-level picture a chain of equivalences
for simple rings: exactly matricial ⟺ all `EL_N(R)` LEF ⟺ all `EL_N(R)` MF.

## Attempts

- **Extract a ring model from group models (dies as stated).**
  - Operator-norm models of `EL_N(R)` send the root subgroups `X_ij ≅ (R,+)` to unitaries. The Steinberg
    relation `[x_12(a), x_23(b)] = x_13(ab)` holds only asymptotically.
  - Nothing produces an approximately multiplicative map `R → M_d`. The additive characters of `(R,+)` seen by the
    unitaries need not assemble into a ring homomorphism.
  - The rank-metric analogue is itself open (`el3-rank-models-factor-through-ring-rank-models`), and
    `un-prior-art` points out that group models must be non-multiplicative on `R` (Leavitt rank collapse
    `rk(1−st) = rk(1−ts)`).
- **Through coordinatization (dies).** Finite images of Steinberg windows need not be linear groups. The
  coordinatization theorem for groups with Steinberg relations in rank `>= 3` recovers a ring only from an
  EXACT group, which gives `R` back and no matricial model.
- **Evidence from Z-subshift rings (positive, non-simple class).** The peer root
  `subshift-elementary-mf-iff-word-edges-lie-on-cycles` states `EL_n(LC(X,F_q) ⋊ Z)` MF ⟺ LEF (`n >= 4`), and in
  the positive case `GL_m` is LEF for every `m`. In that class MF already forces the LEF, tower-type side.
- **Test object (see `stably-finite-simple-rings-have-mf-elementary-groups`, Attempts).** For a free minimal
  aperiodic Z^2 SFT `Ω`, the ring `LC(Ω,F_q) ⋊ Z^2` is simple and stably finite, with Kazhdan linear-sofic
  elementary groups, but exact matricial models are open. If it is not exactly matricial and its elementary
  groups are MF, the strong form of this claim fails.
- **Calibration that any converse must survive.** The Weyl algebra `A_1(Q)` has no finite-dimensional
  representations yet is exactly matricial (`weyl-algebra-is-exactly-matricial`). So a converse cannot pass
  through finite-dimensional representations of `R` in characteristic 0; characteristic-p models are needed.
