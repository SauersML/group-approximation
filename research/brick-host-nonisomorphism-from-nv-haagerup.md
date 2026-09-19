---
rg: 2
id: brick-host-nonisomorphism-from-nv-haagerup
kind: route
title: "An isomorphism of the two groupoids would put the Kazhdan group Gamma inside nV, so the Haagerup property of nV forbids it"
target: brick-groupoid-not-isomorphic-to-kazhdan-host
requires:
  - brin-thompson-groups-nv-are-a-t-menable
  - amenable-purely-infinite-groupoid-full-group-hosts-kazhdan
---

An isomorphism of topological groupoids `φ : G_2^n → 𝒢_W1` induces an isomorphism of
topological full groups `[[G_2^n]] → [[𝒢_W1]]`, because `[[·]]` is defined from the
compact open bisections and `φ` carries those to those.

By `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`, `[[𝒢_W1]]` contains a
copy of `Γ = Z^3 ⋊ SL_3(Z)`, which is infinite and has property (T). Since
`nV ≤ [[G_2^n]]` and in fact `[[G_2^n]] = nV`, the isomorphism would put an infinite
Kazhdan subgroup inside `nV`.

*The equality.* Let `U` be a compact open bisection with `s(U) = r(U) = C^n`. The sets
`U_{μ_1,ν_1} × … × U_{μ_n,ν_n}` form a basis, so `U` is a finite union of basic bisections
contained in it; `s|U` is injective, so removing from each the sources already used gives a
partition of `C^n` into clopen sets, each a finite union of bricks, and a basic bisection
restricted to one brick of its source is again basic. So `U` is a finite disjoint union of
basic bisections, i.e. `π_U` replaces finitely many bricks by finitely many bricks: a brick
map. (Matui, arXiv:1512.01724, abstract: these full groups "are viewed as generalizations of
the higher dimensional Thompson groups".)

A proper conditionally negative definite function on `nV` would restrict to a proper one
on that subgroup, contradicting Delorme–Guichardet (BdlHV Theorem 2.12.4: a group with
property (T) has every conditionally negative definite function bounded) since the
subgroup is infinite. So `brin-thompson-groups-nv-are-a-t-menable` gives the target.

The same argument with `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` gives it
for `𝒢_RS`.

**Use (necessity).** The target is therefore a necessary prerequisite of
`brin-thompson-groups-nv-are-a-t-menable`, and it is implied equally by the weaker
`kazhdan-subgroups-of-brin-thompson-groups-are-finite`. Its failure refutes both, by
exhibiting `Γ ≤ nV`.
