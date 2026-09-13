---
rg: 2
id: type-a-actors-closed-under-type-a-lamp-wreaths
kind: claim
title: A permutational wreath product whose lamp group and top group both carry type (A) actions carries a type (A) action on the product set
distinct_from:
  bh-type-a-class-closed-under-permutational-lamp-wreaths: that allows only FINITE lamp groups acting on themselves; this allows any lamp group with a type (A) action, for instance one containing Z.
  type-a-actions-closed-under-products-and-finite-wreaths: that builds actors from finite direct products and from wreath products with a finite top group Sym_k; this puts a copy of an infinite type (A) actor at every point of an infinite actor set.
  normalizer-image-of-type-a-actor-is-type-a: that enlarges one actor by normalizing permutations of the same set; this builds a new actor on a product set out of two actors.
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**ESTABLISHED** by `type-a-lamp-wreath-with-type-a-lamps-proof`. Elementary. No
novelty is claimed for the check: it is the proof of
`bh-type-a-class-closed-under-permutational-lamp-wreaths` with the finite lamp
group replaced by a type (A) actor, and its finite-presentation half is
Cornulier's theorem. Not independently reviewed.

## Definition used

An action of a group on a set is of type (A) when:
- it is faithful;
- the group is finitely presented;
- every point stabilizer is finitely generated;
- there are finitely many orbits on ordered pairs.

This is the BFFHZ form (arXiv:2503.21882v2, l.120--126, quoted in
`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`). Zaremsky's form
(`type-a-action-gives-boone-higman-for-subgroups`) counts orbits of two-element
subsets instead. The two agree on sets with at least two points: each orbit of
two-element subsets comes from at most two orbits of ordered pairs of distinct
points, and every point orbit meets some two-element subset.

## Statement

Let `Γ` act on a set `S` and `Λ` act on a set `Y`, both of type (A), with
`Λ ≠ 1`. Let `W = Λ wr_S Γ = Λ^(S) ⋊ Γ` be the restricted permutational wreath
product, with `(γ·f)(u) = f(γ^(-1) u)` and
`(f, γ)(f', γ') = (f·(γ·f'), γγ')`. Then

```text
(f, γ) · (s, y) = (γ s, f(γ s) · y)        on  S × Y                     (LW)
```

is an action of type (A). The stabilizer of `(s, y)` is
`(Stab_Λ(y) at s × Λ^(S∖{s})) ⋊ Stab_Γ(s)`.

**Consequence.** By `type-a-action-gives-boone-higman-for-subgroups`, every subgroup
of `W` has solvable word problem if it is finitely generated, and embeds in a
finitely presented simple group.

**Where it is used.** `permutational-boone-higman-closed-under-wreath-products`
takes `Γ` to be BFFHZ's relative automorphism actor, on which the input acts
freely, and `Λ` to be any actor containing the lamp group.
