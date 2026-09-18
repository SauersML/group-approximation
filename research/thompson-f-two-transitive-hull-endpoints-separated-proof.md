---
rg: 2
id: thompson-f-two-transitive-hull-endpoints-separated-proof
kind: route
title: Composing half-supported elements gives the two triangle rules, and a value that is both max-attained-twice and min-attained-twice is constant, hence an F-fixed point
target: thompson-f-two-transitive-hull-endpoints-are-separated
requires:
  - thompson-f-two-transitive-hull-endpoints-are-rational
---

Notation as in the target. Put `I^-(ω,ω') = {x : ω' ∈ F_x^- ω}` and
`I^+(ω,ω') = {x : ω' ∈ F_x^+ ω}`. By item 1 of
`thompson-f-two-transitive-hull-endpoints-are-rational`, `I^-` is an up-set and
`I^+` a down-set of `(0,1)`, both nonempty and proper; `η` and `ξ` are symmetric,
`F`-equivariant, and `ξ ≤ η`.

**Step 1 (openness at the endpoints).** If `x > η(ω,ω')` then `x ∈ I^-(ω,ω')`:
some `x' < x` lies in `I^-`, and `I^-` is an up-set. Likewise `x < ξ(ω,ω')`
implies `x ∈ I^+(ω,ω')`.

**Step 2 (triangle rule for `η`).** Let `x > max(η_{12}, η_{23})`, where
`η_{ij} = η(ω_i,ω_j)`. By Step 1 there are `a, b ∈ F_x^-` with `aω_1 = ω_2` and
`bω_2 = ω_3`. Then `ba ∈ F_x^-` and `baω_1 = ω_3`, so `x ∈ I^-(ω_1,ω_3)` and
`η_{13} ≤ x`. Letting `x` decrease to the maximum gives
`η_{13} ≤ max(η_{12}, η_{23})`.

**Step 3 (triangle rule for `ξ`).** Symmetrically, for `x < min(ξ_{12}, ξ_{23})`
there are `c, d ∈ F_x^+` with `cω_1 = ω_2`, `dω_2 = ω_3`, so `dc ∈ F_x^+` maps
`ω_1` to `ω_3`. Hence `ξ_{13} ≥ x`, and `ξ_{13} ≥ min(ξ_{12}, ξ_{23})`.

Applying Steps 2 and 3 to all three relabelings of a triple, using symmetry,
the largest of `η_{12}, η_{13}, η_{23}` is at most the maximum of the other two,
so it is attained at least twice; and the smallest `ξ`-value is at least the
minimum of the other two, so it is attained at least twice. This is item 1.

**Step 4 (all pairs are alike).** The relation `R = {(ω,ω') : ξ(ω,ω') = η(ω,ω')}`
on ordered pairs of distinct points is `F`-invariant, by equivariance of `ξ` and
`η`. Since `F` is transitive on ordered pairs of distinct points, `R` is empty
or contains every pair.

**Step 5 (the case `R` = everything is impossible).** Suppose `ξ = η = d` on all
pairs. In a triple `ω_1, ω_2, ω_3`, the largest value of `d` is attained at least
twice (item 1 for `η`) and the smallest value is attained at least twice (item 1
for `ξ`). Among three numbers, if the maximum and the minimum are each attained
at least twice, all three are equal: otherwise the maximum and minimum differ and
together need at least four entries. So `d` is constant on the three pairs of
every triple.

Any two pairs are joined by triples: pairs sharing a point lie in one triple, and
for disjoint pairs `{ω_1,ω_2}`, `{ω_3,ω_4}` we get
`d(ω_1,ω_2) = d(ω_1,ω_3) = d(ω_3,ω_4)` from the triples `{ω_1,ω_2,ω_3}` and
`{ω_1,ω_3,ω_4}`. Hence `d` is a constant `c ∈ (0,1)`. For `g ∈ F` and any pair,
equivariance gives `g(c) = g(d(ω,ω')) = d(gω,gω') = c`, so every element of `F`
fixes `c`. But `F` fixes no point of `(0,1)`: for every `c ∈ (0,1)` there is an
element of `F` with `g(c) ≠ c` (for example one with `g(t) > t` on all of
`(0,1)`). This is a contradiction.

So `R` is empty, and with `ξ ≤ η` we get `ξ(ω,ω') < η(ω,ω')` for every pair.
This is item 2. ∎
