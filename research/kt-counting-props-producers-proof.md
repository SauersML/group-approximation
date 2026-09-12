---
rg: 2
id: kt-counting-props-producers-proof
kind: route
title: Lean proofs of the one-sided, concentration and transport producers
target: kt-counting-props-producers
requires: []
artifacts:
  - GroupApproximation/KunThom/CountingEndgameProps.lean
  - GroupApproximation/KunThom/CountingEndgamePropsScale.lean
  - GroupApproximation/KunThom/CountingEndgamePropsMedian.lean
  - GroupApproximation/KunThom/CountingEndgamePropsOneSided.lean
  - GroupApproximation/KunThom/CountingEndgamePropsSelect.lean
  - GroupApproximation/KunThom/CountingEndgamePropsCounting.lean
---

A derivation in Lean. The modules are imported by `GroupApproximation.lean` and
built green by the Bowen–Chapman probe (tags 0912-142742-32070, 0912-143059-52238,
0912-143628-84665 and 0912-144801-43926). An axiom driver (tag 0912-145249-68503)
prints the closures of the three producers and the main lemmas. Every one uses only
`propext`, `Classical.choice` and `Quot.sound`.

1. **Sizes and scales** (tex lines 1133–1156). Along every arrow of a scaled cluster
   groupoid the block size at most doubles, because matched scales agree up to
   `11 / 10` and the scale is a fixed fraction of the size. The cleanliness scale
   `min (√e + 1/(n+1)) (1/2)` of a vanishing density `e` vanishes, and `e` vanishes
   against it.
2. **One-sided inequalities** (tex lines 1140–1193). At a matched object with clean
   match, the orbit of the match loses at most a `ζ` fraction and isotropy grows. So
   the arrow count rises by at most `1 + 2ζ`. The non-clean orbits have weight at
   most `1 / (ζ (1 - 1/2))` times the unretained weight, by double counting over
   orbits. Pulling them back along the matching at most doubles the weight.
3. **Concentration** (Lemma 4.4) is `blockRatio_negligible`.
4. **Counting** (tex lines 1218–1313).
   - The squared ratio bound at `η ≤ 1/16`, isotropy monotonicity and cleanliness
     bound the orbit ratio by `1 + 16η` and the isotropy ratio by
     `(1 + 16η) / (1 - ζ)`.
   - Once `1 + 16η < 2 (1 - ζ)`, every good object is the image of a selected
     object, and the lift of the finite endgame applies.
   - The complement of the good objects lies in six families of negligible weight.
