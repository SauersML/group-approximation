---
rg: 2
id: every-finitely-presented-group-embeds-in-an-f-infinity-group
kind: claim
title: "Every finitely presented group embeds in a group of type F_infinity"
distinct_from:
  every-type-fn-group-embeds-in-a-type-fn-plus-1-group: that asks for an F_{n+1} host for each group of type F_n and is implied by this claim; this asks for an F_infinity host, equivalently one F_infinity group containing a universal finitely presented group
  some-finitely-presented-group-embeds-in-no-f-infinity-group: that is the negation of this claim
---

Every finitely presented group `G` admits an injective homomorphism into some
group of type `F_∞`. Groups of type `F_n` with `n >= 2` are finitely presented
and every finitely presented group is of type `F_2`, so this is exactly the
affirmative answer to the second part of Zaremsky Problem 1.1 (root
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`). It implies the first
part.

Equivalent forms:

1. a universal finitely presented group `U` (Higman 1961) embeds in a group of
   type `F_∞`;
2. every finitely generated recursively presented group embeds in a group of
   type `F_∞` (the second half of Question 1.3 of Fournier-Facio--Zaremsky,
   arXiv:2607.21727v1);
3. every finitely generated recursively presented group embeds in a
   recursively presented group of type `FP_∞`. Theorem A of the same paper
   (with `n = ∞`) gives 3 ⇒ this claim; the converse holds because an `F_∞`
   host is finitely presented, hence recursively presented, and of type
   `FP_∞`.

## Attempts

- The attempts recorded on
  `every-type-fn-group-embeds-in-a-type-fn-plus-1-group` apply here at every
  level at once: the rope trick is dead above `FP_2`, vertex-group hosts over
  `FP_∞` edge groups are dead, and twisted Brin--Thompson hosts need the input
  to be of type `F_∞` already.
- A host containing `U` contains Thompson's group `F` (cohomological dimension
  `∞`) and every finite group, so it has infinite cohomological dimension and
  torsion of every order. Thompson-like groups of type `F_∞` have these
  features; groups with a finite-dimensional classifying space do not.
