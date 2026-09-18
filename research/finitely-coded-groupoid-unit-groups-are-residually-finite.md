---
rg: 2
id: finitely-coded-groupoid-unit-groups-are-residually-finite
kind: claim
title: In an effective finitely coded Li groupoid satisfying condition (F), every unit group embeds in a product of finite symmetric groups of cylinders, so it is residually finite
distinct_from:
  finitely-coded-cantor-actions-give-type-a-hosts: that allows arbitrary unit groups and concludes that complexity must sit in them; this shows that in the effective case the unit groups are residually finite groups acting on locally finite rooted trees of cylinders, i.e. self-similar-type groups.
  almost-automorphism-torsion-subgroups-are-rf: that proves residual finiteness of torsion subgroups of almost-automorphism groups; this proves residual finiteness of the unit groups of a Li category, with no torsion hypothesis.
  li-coded-certificates-cannot-reach-hard-sft-hosts: that uses this node as its unit-group input for the master-route bridge.
---

**ESTABLISHED** (lane proof, bh-g3-libridge 2026-09-18, inline below; not independently
reviewed; no priority claimed — the argument is the standard "automorphisms of a locally finite
rooted tree form a profinite group", transported to Li's categories).

## Setting

`ℭ` is a left cancellative, finitely aligned small category with finitely many objects,
`𝒢 = I_l ⋉ ∂Ω` is Li's boundary groupoid (arXiv:2110.04505v2, §2; Li 2021a), and
`X(v) = ∂Ω(v)` is the boundary over the object `v`. For `c ∈ vℭ` the *cylinder* of `c` is
`cX(d(c)) ⊆ X(v)`. Assume:

- **(LF) local finiteness.** A degree map `d : ℭ -> P` is given (any monoid `P`, `d^{-1}(1) = ℭ^*`),
  and for every object `v` and `p ∈ P` there are only finitely many cylinders `cX(d(c))` with
  `c ∈ vℭ`, `d(c) = p`. (Equivalently: finitely many morphisms of each degree into `v` modulo
  right multiplication by units, since `cX = c'X` iff `cℭ = c'ℭ` iff `c' ∈ cℭ^*`.)
- **(Eff)** `𝒢` is effective (a groupoid of germs).
- **(F)** Li's condition (F) (arXiv:2110.04505v2, l.1454) for `U = X(v)`: for units
  `a, b ∈ ℭ^*(v,v)`, `[a, X(v)] = [b, X(v)]` implies `a = b`.

## Statement

For every object `v`, the map `ℭ^*(v,v) -> ∏_{p ∈ P} Sym(Cyl_p(v))`, recording how a unit permutes
the finite set `Cyl_p(v)` of degree-`p` cylinders, is an injective homomorphism. In particular
every unit group `ℭ^*(v,v)` is residually finite, and its closure in `Homeo(X(v))` is profinite.

## Proof

1. **Units permute cylinders of each degree.** For `u ∈ ℭ^*(v,v)` and `c ∈ vℭ`, the partial
   homeomorphism of `u` maps `cX(d(c))` onto `(uc)X(d(uc))`, and `d(uc) = d(c)`. So `u` permutes
   `Cyl_p(v)`, which is finite by (LF), and this is a homomorphism `ℭ^*(v,v) -> Sym(Cyl_p(v))`.
2. **Fixing all cylinders means acting trivially.** Points of `∂Ω(v)` are characters `χ` on the
   semilattice of constructible right ideals. For finitely aligned `ℭ` these ideals are finite
   unions of principal ideals `cℭ` (recalled from Li 2021a, not re-read), so `χ` is determined by
   the values `χ(cℭ)`. The action is `(u.χ)(Y) = χ(u^{-1}Y)`. If `u` fixes every cylinder, then
   `u^{-1}cℭ = cℭ` for every `c ∈ vℭ`, so `u.χ = χ` for every `χ`.
3. **Trivial action means `u = 1_v`.** If `u` acts trivially on the open set `X(v)`, its bisection
   `[u, X(v)]` lies in the isotropy of `𝒢`. By (Eff) the interior of the isotropy is the unit space,
   so `[u, X(v)] = [1_v, X(v)]`, and (F) gives `u = 1_v`.
4. So the product map is injective. A subgroup of a product of finite groups is residually finite. ∎

## Consequences

- **Units are self-similar-type groups.** In every effective finitely coded host (the hosts of
  `finitely-coded-cantor-actions-give-type-a-hosts`: `nV`, `2V_τ`, Röver–Nekrashevych groups,
  tree-product, Ã₂ and Euclidean-building lattices, `CT_P(Z)`), each unit group acts faithfully and
  self-similarly on the locally finite rooted tree of its cylinders.
- **Hard inputs cannot be units.** An infinite simple group, e.g. any input of the reduced class of
  `boone-higman-iff-simple-kazhdan-decidable-inputs`, embeds in no unit group of such a host. It can
  only enter the full group through elements that mix prefix moves with units.
- **Where the complexity budget sits.** If a finitely coded host is to contain groups of arbitrarily
  hard word problem, the hardness has to be carried either by the prefix-move combinatorics or by
  residually finite unit groups acting on trees. The first option is capped at exponential time for
  finite-state data (`finite-state-li-coded-full-groups-have-exponential-word-problem`).

## Lesson for general BH

Li's framework lets the unit groups be anything, but effectiveness, which simplicity and type (A)
both need, forces them to act faithfully on locally finite rooted trees, hence to be residually finite
and self-similar in the categorical sense. So "put the complexity in the units" is the same demand as
the open root `fp-self-similar-groups-with-arbitrarily-hard-word-problem`, in its multi-object
(Zappa–Szép) form. The finitely coded route and the self-similar route to hard hosts are one problem.
