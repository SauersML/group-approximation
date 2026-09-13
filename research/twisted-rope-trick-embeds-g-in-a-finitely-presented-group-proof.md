---
rg: 2
id: twisted-rope-trick-embeds-g-in-a-finitely-presented-group-proof
kind: route
title: "The relations of G follow from the finitely many twisted conjugation relations"
target: twisted-rope-trick-embeds-g-in-a-finitely-presented-group
requires: []
---

**Item 1.** A vertex group embeds in its HNN extension (Higman–Neumann–Neumann,
J. London Math. Soc. 24 (1949)). `G` is a factor of the vertex group `P × G`.

**Item 2.** Let `K'` be the presented group.

*A map `K' → Hig = Hig_{ι,ι'}(G)`.* Send `s ↦ (s, 1)`, `x_i ↦ (1, x_i R)` and
`t ↦ t`. The relations `Q` and `[s, x_i]` hold in `P × G`. The conjugation
relations are the HNN relations for the generators `y = x_i^(1)`, where
`π(y) = x_i R`, and `y = x_i^(2)`, where `π(y) = 1`.

*Presentation of `Hig`.* An HNN extension of `A` is presented by a presentation
of `A`, the letter `t`, and `t φ_1(y) t^{-1} = φ_2(y)` for `y` in a generating
set of the associated subgroup. Conjugation by `t` and the associated maps are
homomorphisms, so the relations for generators give them for all `y`. A
presentation of `A = P × G` is `S ∪ {x_i}` with relations `Q`, `[s, x_i]`, and
all `r(x) = 1` for `r ∈ R`. So `Hig` is `K'` with the extra relations
`r(x) = 1`, `r ∈ R`, and it suffices to derive these in `K'`.

*Derivation.* For a word `w` in the letters `x_i`, write `w(u)`, `w(v)`,
`w(u')`, `w(v')` for the words in `S` obtained by substituting `u_i`, `v_i`,
`u'_i`, `v'_i`.

- Conjugation by `t` is an automorphism of `K'`, so
  `t w(u) t^{-1} = w(u'x)`, where `w(u'x)` substitutes `u'_i x_i` for `x_i`.
  The words in `S` commute with every `x_j` in `K'` (relations `[s, x_j]`), so
  `w(u'x) = w(u') w(x)`. Likewise `t w(v) t^{-1} = w(v')`.
- Let `r ∈ R`. In `L` we have `r^(1) = r^(2)`, so `ι(r^(1)) = ι(r^(2))` and
  `ι'(r^(1)) = ι'(r^(2))` in `P`. That is, `r(u) = r(v)` and `r(u') = r(v')`
  in `P`, and both are consequences of `Q`, so they hold in `K'`.
- Hence in `K'`:
  `r(u') r(x) = t r(u) t^{-1} = t r(v) t^{-1} = r(v') = r(u')`, so `r(x) = 1`.

So the two groups have the same generators and relations, and the map above
is an isomorphism. If `S` and `Q` are finite, the presentation is finite.

The last bullet of the claim follows from the same computation. The only
relations of `P` used are `r(u) = r(v)` and `r(u') = r(v')`, together with the
relations of `P` needed to identify the words `u_i, v_i, u'_i, v'_i`. When
these follow from finitely many relations and the conjugation relations, the
presentation stays finite even if `P` is infinitely presented.
