---
rg: 2
id: minimal-sfts-with-a-finite-modification-are-not-quantum-rigid
kind: claim
title: Over any finitely generated group, a minimal subshift of finite type in which two configurations differ on a nonempty finite set is not quantum rigid at any scale
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that kills Z^2 SFTs of positive entropy through recurrence of an ambiguous annulus; this uses no entropy and no amenability, only minimality and one finitely supported modification, over every finitely generated group.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that classifies the first-order obstructions over Z^2; this is one explicit first-order obstruction, available over every group.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines D-quantum rigidity over any group and records the wall certificate as its calibration; this applies the certificate to finitely supported modifications of minimal shifts.
artifacts:
  - research/artifacts/gq-bh-bh-g2-obstruct-kill-attempt.md
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).**

## Setting

`Λ` is an infinite finitely generated group with a word metric `d`. `X ⊆ A^Λ` is an SFT whose forbidden
patterns lie in `B_r`. D-quantum families and D-quantum rigidity over a field `k` (conditions Q1–Q3)
are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`. Always `D >= r`. For `x, y ∈ X`,
`Δ(x, y) = {g : x(g) != y(g)}`. A *modification* of `x` is any `y ∈ X` with `y != x`.

## Lemma (far modifications)

If some `x ∈ X` has modifications `y_1, y_2` with `d(Δ(x,y_1), Δ(x,y_2)) > 2D`, then `X` is not
`D`-quantum rigid over any field.

*Proof.* Put `Δ_i = Δ(x, y_i)`. Let `z` equal `y_i` on `Δ_i` and `x` elsewhere.
- **`z ∈ X`.** An `r`-ball meeting `Δ_1` misses `Δ_2`, because `2D >= 2r`. On that ball `z = y_1`,
  since `y_1 = x` off `Δ_1`. The same holds for `Δ_2`, and every other `r`-ball reads `x`.
- **The wall.** Put `P = Δ_1`, `M = N_(2D)(Δ_1) \ Δ_1` and `N = Λ \ N_(2D)(Δ_1)`. Then:
  - `x = z` on `M`, because `M` misses `Δ_2`;
  - `x != z` somewhere on `P`, and on `Δ_2 ⊆ N`;
  - every ball `B_D(p)`, and every pair of sites at distance `<= 2D`, lies in `P ∪ M` or in `M ∪ N`.
- **The family.** The wall certificate of `positive-entropy-sft-crossed-products-are-not-fp-proof`,
  item 1, then works verbatim over `Λ`. On `W = k^2`, take `E_a(q)` diagonal with entries
  `([x(q)=a], [z(q)=a])` in the basis `(e_1, e_2)` on `P ∪ M`, and in the basis `(e_1 + e_2, e_2)` on
  `N`. This is a noncommuting D-quantum family. ∎

## Theorem

Let `X` be minimal, and suppose `x ≠ x'` in `X` differ on a finite set `F`. Then `X` is not
`D`-quantum rigid for any `D >= r`, over any field.

*Proof.* Fix `D` and put `R = N_(2D)(F)`, a finite set.
- Since `X` is minimal, `x` is uniformly recurrent. So the set of `g` with `x(g h) = x(h)` for all
  `h ∈ R` is syndetic, and it contains `g` with `d(F, gF) > 4D`.
- Let `y_2` be `x` with the translate of the pattern `x'|R` written on `gR`.
  - On `gR \ gF` this agrees with `x`, because `x = x'` on `R \ F` and `x|gR` is the translate of
    `x|R`.
  - Every `r`-ball meeting `gF` lies in `gR`, and there `y_2` reads a translate of the legal pattern
    `x'|R`. Every other `r`-ball reads `x`.
  - So `y_2 ∈ X`, and `Δ(x, y_2) = gF`.
- With `y_1 = x'`, `Δ(x, y_1) = F` is at distance `> 2D` from `gF`, so the Lemma applies. ∎

## Consequences

1. **Minimal rigid SFTs are finitely rigid.** If a minimal SFT is `D`-quantum rigid for some `D`,
   then no two of its configurations differ on a nonempty finite set. Equivalently, every occurring
   pattern on an annulus `N_w(F) \ F` with `w >= r` has exactly one legal filling of `F`. The two forms
   agree because refilling inside such an annulus is legal whenever `w >= r`.
2. **Relation to entropy.** Over amenable `Λ`, a minimal SFT with a finite modification has positive
   entropy: syndetic, pairwise far occurrences of the ambiguous annulus can be refilled independently.
   So over `Z^2` this theorem is the entropy-free form of Proposition 4 of
   `research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md`.
   - Over non-amenable `Λ`, for example `Λ_0 × F_2` or `F_2 × F_2`, there is no entropy to appeal to,
     and the theorem is a new, independent constraint on the G2 crux of
     `research/artifacts/gq-bh-synthesis-master-route.md`.
3. **Calibration.**
   - Labbé's shift is minimal. Its same-fibre differences are full fault lines
     (`labbe-shift-is-wall-rigid`), so it has no finite modification. This is consistent.
   - Ledrappier's shift is rigid (`ledrappier-crossed-product-is-finitely-presented`). A finite change of
     a Ledrappier configuration propagates along the permutive rule, so there is no finite modification
     there either. This is also consistent.
   - The full shift over any infinite `Λ` has finite modifications and is not rigid (it is not
     minimal, but the Lemma applies directly).

## Lesson for general BH

Every candidate for the master route's decisive object, a quantum rigid free minimal SFT over a
one-ended `Λ`, must be *finitely rigid*: no configuration can be changed on a finite set. Over
amenable groups this is just zero entropy. Over the non-amenable envelopes that design rule 3 prefers,
it is a separate constraint with no entropy behind it.
- **What it rules out:** every construction in which finite local decorations can be flipped
  independently, such as optional markers inside hierarchical tilings, or finite "switches" used to
  encode computation.
- **What remains:** allowed modifications must be infinite and coarsely connected. That is exactly
  the first-order (wall) regime, and beyond it only genuinely contextual operator families can refute
  rigidity.
