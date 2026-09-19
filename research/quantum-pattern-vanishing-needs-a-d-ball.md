---
rg: 2
id: quantum-pattern-vanishing-needs-a-d-ball
kind: claim
title: "A non-occurring pattern kills its quantum product when its support lies in a D-ball, but not merely when its diameter is at most 2D; the splitting-rigidity lemma (L0) needs the ball form, which all its uses satisfy"
distinct_from:
  locally-finite-splittings-preserve-rigid-sft-compactifications: that is the closure of the class C under locally finite splittings; this is only the corrected form of its operator lemma (L0), with a calibration showing that the form stated there is false, and a check that every use of it is covered by the corrected form.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines D-quantum families and derives rigidity from finite presentation; this is a lemma about which pattern products a D-family must kill.
---

**ESTABLISHED** by `quantum-pattern-vanishing-needs-a-d-ball-proof` (audit lane bh-audit, 2026-09-19).

The setting is that of `fp-v-times-subshift-full-groups-force-quantum-rigidity`. `Λ` is a finitely
generated group, `X ⊆ A^Λ` is a subshift, and `(E_a(q))` is a `D`-quantum family (Q1–Q3) on a vector
space over a field `k`.

1. **Ball form (true).** Let `F ⊆ B_D(p)` for some `p ∈ Λ`, and let `β` be a pattern on `F` that does
   not occur in `X`. Then the factors `E_(β(f))(f)`, `f ∈ F`, pairwise commute, and
   `∏_(f ∈ F) E_(β(f))(f) = 0`.
2. **Diameter form (false).** The statement "if `diam F ≤ 2D` and `β` does not occur, the product
   vanishes" fails. Take `Λ = Z × Z/5` with generators `(±1,0), (0,±1)`, and `D = 1`. Let `X` be the
   SFT in which every column `{n} × Z/5` carries exactly one `1`. Let `E_a(q) = [a = 0]`, scalars on
   `k`: this is the all-zero configuration. It is a commuting `1`-quantum family, because every
   `B_1`-window of the all-zero configuration occurs in `X`. But the column `F = {0} × Z/5` has
   diameter `2 = 2D`, the all-zero pattern on `F` does not occur, and its product is `1`.
3. **Consequence for `locally-finite-splittings-rigid-compactification-proof`.** Its lemma (L0) is
   stated in the diameter form. That form is false in general, by item 2. However, every use of (L0)
   in that proof applies it to a set contained in a `D`-ball, so item 1 covers each one, and the
   proof stands:
   - (L1) and (L2) use two sites at distance at most the rule radius `r ≤ D`;
   - the sink step in Section 4 uses `hB^A_D ⊆ B^Λ_D(h)`, since `d_Λ ≤ d_A`.
