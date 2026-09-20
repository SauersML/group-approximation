---
rg: 2
id: burger-laurent-pair-not-in-wobbling-group-from-selberg-proof
kind: route
title: "Congruence point-kernel orbits have Cheeger constant O(1/size) and unbounded size; the Selberg property bounds the Cheeger constant of every congruence quotient below"
target: burger-laurent-pair-is-not-in-the-wobbling-group
requires: [burger-laurent-pair-wobbling-point-kernels-are-congruence, laurent-sl2-positive-characteristic-has-selberg-property]
---

Suppose `Γ_p ≤ W(Z)`. Use the notation of
`burger-laurent-pair-wobbling-point-kernels-are-congruence`. `E = EL_2(R) = SL_2(R)`, since
`R` is Euclidean. Fix the finite generating set `S` of `E` from
`laurent-sl2-positive-characteristic-has-selberg-property`, with constant `c > 0`. Lift `S` to
`S̃ = {(s, 0)} ⊂ Γ_p` and put `D = Σ_{s∈S̃} d(s)`.

**Step 1 (quotients keep the Cheeger bound).** Let `J ≠ 0` and let `π: E/E(J) → Q` be a surjection of
transitive `E`-sets. All fibres of `π` have the same size `k`. For `A ⊂ Q` with `|A| ≤ |Q|/2`, put
`Ã = π^{-1}(A)`. Then `|Ã| = k|A| ≤ |E/E(J)|/2`. Also `sã ∉ Ã` iff `sπ(ã) ∉ A`, so
`|sÃ \ Ã| = k|sA \ A|`. Hence

`Σ_s |sA \ A| / |A| = Σ_s |sÃ \ Ã| / |Ã| ≥ c`.

So every Schreier graph `(Q, S)` of this form has Cheeger constant at least `c`.

**Step 2 (contradiction).** Item 3 of the congruence node gives each `Q_x` as a quotient of
`E/E(I_x)` with `I_x ≠ 0`. By Step 1, its Cheeger constant is at least `c`. Item 5 bounds it by
`2D/⌊|Q_x|/2⌋`. Item 4 gives `x` with `|Q_x| > 2(2D/c + 1)`, and for such `x` the upper bound is
below `c`. Contradiction. So `Γ_p ⊄ W(Z)`.

**Step 3 (`[[X]]`).** `[[X]]` embeds in `W(Z)` along a dense orbit, by Step 6 of
`wobbling-normal-relative-t-locally-finite-proof`. So `Γ_p ⊄ [[X]]`.
