---
rg: 2
id: thompson-f-monomial-doubling-width-bounds-degree-proof
kind: route
title: Pad on the right with x_L for one direction; for the other, split by the last letter, which pushed letters cannot imitate once the degree reaches L
target: thompson-f-monomial-doubling-width-bounds-degree
requires: []
artifacts:
  - experiments/thompson-f-2026-09-17/last_letter_fibres.py
  - experiments/thompson-f-2026-09-17/width_degree_law.py
---

**Left multiplication on normal forms.** Let `w = x_(w_0) ... x_(w_(D-1))` be a normal form
(`w_0 <= ... <= w_(D-1)`). The normal form of `x_j w` comes from the relation
`x_j x_i = x_i x_(j+1)` (`i < j`): while the current letter satisfies `w_k < j`, keep it and raise `j`
by one; then insert `x_j`. So `x_j` either stops before some position `k`, where it inserts the value
`j + k <= w_k`, or it passes all `D` letters and is appended with value `j + D`. A letter `x_0`
never passes the first letter, because `w_0 >= 0`. For `s = x_(s_1) ... x_(s_d)` in normal form,
`s w` applies `x_(s_d)` first, then `x_(s_(d-1))`, and so on.

**Item 1.** Right multiplication by `x_L` is injective, and `S (Y x_L) = (S Y) x_L`. For
`Y ⊆ M_(D,L)` we have `Y x_L ⊆ M_(D+1,L)`, since appending the largest allowed letter keeps normal
form. So `|S(Y x_L)|/|Y x_L| = |S Y|/|Y|`.

**Lemma (pushed letters are large).** Let `y ∈ M_(D,e)` and `s ∈ S`. Every letter of the normal
form `u = s y` is either `<= e` or `>= D+1`, and all letters `>= D+1` come after all the others.

*Proof.* Induct on the letters of `s`, from right to left. Suppose the current word `v` is `y`
with some letters inserted: those `<= e` sit among the letters of `y`, and a tail of letters
`>= D+1` sits at the end. A new letter `x_a` that stops before a letter of value `<= e` is inserted
with value `<= e`. If `x_a` reaches the tail, it has passed at least the `D` letters of `y`, and
`a >= 1` because `x_0` stops at once. So its pointer is `>= a + D >= D+1`, and whether it stops
inside the tail or is appended, its value is `>= D+1`. Letters behind the insertion point do not
change. ∎

**Item 2: `Λ_S(D+1,L) >= Λ_S(D,L)` whenever `D+1 >= L`.**

*Splitting by last letter.* Let `Y ⊆ M_(D+1,L)` be nonempty. Split it by last letter as
`Y = ⊔_(e <= L) Y_e x_e` with `Y_e ⊆ M_(D,e) ⊆ M_(D,L)`. As group elements,
`S(Y_e x_e) = (S Y_e) x_e`.

*The image determines its last letter.* Take `u ∈ S Y_e`. By the lemma, `u = u' u''`, where the
letters of `u'` are `<= e` and those of `u''` are `>= D+1 >= L`.
- If `u''` has a letter `p <= e`, then `p = e = L = D+1`. Put such letters into `u'`.
- Every remaining letter of `u''` is `> e`. The relation `x_i x_e = x_e x_(i+1)` (`i > e`) gives
  `z = u x_e = u' x_e u'''`. This is a normal form, and every letter of `u'''` is `>= D+2 > L`.

So the largest letter of `z` that is `<= L` is exactly `e`. Hence `z` determines `e`, and by
cancellativity it determines `u = z x_e^(-1)`.

*Conclusion.* The sets `(S Y_e) x_e` for distinct `e` are pairwise disjoint, and
`|S(Y_e x_e)| = |S Y_e|`. Therefore

`|S Y| = sum_e |S Y_e| >= Λ_S(D,L) sum_e |Y_e| = Λ_S(D,L) |Y|`.

Together with item 1, `Λ_S(D,L) = Λ_S(L-1,L)` for every `D >= L-1`.

**Item 3.** `S` is homogeneous, so `S Y` is the disjoint union of the sets `S Y^(D)` over the
homogeneous components `Y^(D)` of `Y`. It is enough to show
`|S Y^(D)| >= Λ_S(min(D, L-1)) |Y^(D)|`.
- If `D <= L-1`: `Λ_S(D,L) >= Λ_S(D)` by definition.
- If `D >= L-1`: by item 2, `Λ_S(D,L) = Λ_S(L-1,L) >= Λ_S(L-1)`.

`Λ_S` is nonincreasing in `D` (item 2 of
`thompson-f-monomial-doubling-ratio-is-a-finite-computation`). So the component of largest degree
`D_Y` gives the weakest bound, `Λ_S(min(D_Y, L-1))`, and that bound holds for all of `Y`.

**Obstruction for `P_(2,2)`.** Suppose `|S Y| < 2|Y|` for `S = S_(3,5)`. Then some homogeneous
component satisfies `|S Y^(D)| < 2|Y^(D)|`. The exact values on main give
`Λ_(S_(3,5))(n) >= Λ_(S_(3,5))(12) ≈ 2.6676 > 2` for all `n <= 12`. By item 3 this component has
`min(D, L_(Y^(D)) - 1) >= 13`, where `L_(Y^(D))` is its largest letter.

**Where the argument stops.** Take `Y ⊆ M_(D+1,L)` with `D+1 < L`. The lemma's pushed value `D+1`
can then be a letter `< L` that is not the last letter, and different last letters really
coincide. Example with `S = X_2` and `Y ⊆ M_(5,6)`: `x_1 · x_0^5 = x_0 · x_0^4 x_6`.
`last_letter_fibres.py` finds cross-fibre images in degree `L-1` for `X_2` and `S_(3,5)` at
`L = 6, 7`, and none in degree `L` at `L = 5, 6, 7`. The sharper law
`Λ_S(D,L) = Λ_S(min(D, L-r))`, with `r` the largest letter of `S`, needs a finer fibration. It is
recorded as open in `thompson-f-monomial-doubling-ratio-depends-only-on-width`.
