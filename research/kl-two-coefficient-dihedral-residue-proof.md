---
rg: 2
id: kl-two-coefficient-dihedral-residue-proof
kind: route
title: Localize to the loop subgroup and apply the hyperlinear theorem
target: kl-two-coefficient-residue-word-with-involution-loops-injects
requires:
  - kl-failure-localizes-to-the-coefficient-subgroup
  - kervaire-laudenbach-holds-for-hyperlinear
---

The coefficients occurring in `w = t^5 y t^(-1) x` are `y` and `x`. So the
coefficient subgroup of `kl-failure-localizes-to-the-coefficient-subgroup` is
`A = <x, y>`, and `w in A * <t>` with `deg_t(w) = 4 != 0`.

If `A` is hyperlinear, `kervaire-laudenbach-holds-for-hyperlinear` gives that
`A -> (A * <t>)/<<w>>` is injective. Then
`kl-failure-localizes-to-the-coefficient-subgroup` gives that
`G -> (G * <t>)/<<w>>` is injective.

**Involutions.** If `x^2 = y^2 = 1`, the homomorphism `C_2 * C_2 -> A` sending
the two generators to `x` and `y` is onto. `C_2 * C_2` is the infinite dihedral
group. It is virtually infinite cyclic, so it and all its quotients are
amenable. Amenable groups are sofic, and sofic groups are hyperlinear. So `A` is
hyperlinear.

**Unnormalized words.** The automorphism `t -> s u^(-1)` of `G * <t>` fixes `G`,
so it maps the normal closure of a word onto that of its image, and injectivity
of `G` is unchanged.
