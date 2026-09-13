---
rg: 2
id: thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3-proof
kind: route
title: The short relators present two cone-permutation groups, and the long words carry the rest
target: thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
requires:
  - bleak-quick-finite-presentations-of-thompson-v
---

Numbering follows the claim. Checks: `experiments/thompson-v-models/amalgam_orders.py`, run on MSI.

**Rigid cone permutations.** Fix a partition `R` of the Cantor set into cones. A permutation `pi` of
`R` gives the element of `V` that replaces the prefix of each cone by the prefix of its image.
- This is a homomorphism `Sym(R) -> V`: composites of rigid cone maps are rigid.
- It is injective: a nontrivial `pi` moves some cone onto a disjoint cone.

**1.**
- `a` and `b` are the rigid maps of the transposition `(00 01)` and the 3-cycle `(01 10 11)` of `Q`.
  The closure computation gives `|<a, b>| = 24`, so `<a, b> = Sym(Q)`. There `ab` is the 4-cycle
  `(00 10 11 01)`, so `a^2 = b^3 = (ab)^4 = 1`.
- The group `<a, b | a^2, b^3, (ab)^4>` has order 24 by coset enumeration (sympy `FpGroup.order`). It
  maps onto `Sym(Q)`, so the map is an isomorphism.

**2.**
- `a` and `c` are the rigid maps of the transpositions `(00 01)` and `(1 00)` of `P`. They generate
  `Sym(P)`, and `ac` is the 3-cycle `(00 01 1)`.
- In `<a, c | a^2, c^2, (ac)^3>`, put `u = ac`. Then `u^3 = 1` and `a u a = ca = u^-1`, so `<u>` has
  index at most 2 and the order is at most 6. The presented group maps onto `Sym(P)`, so the map is
  an isomorphism. Coset enumeration agrees: order 6.

**3.** Let `g in <a, b> ∩ <a, c>`.
- As an element of `Sym(Q)`, `g` maps cones of measure `1/4` rigidly onto cones of measure `1/4`,
  so it preserves the uniform measure.
- As an element of `Sym(P)`, if `g` moved the cone `1` onto `00` or `01`, it would map a set of
  measure `1/2` onto one of measure `1/4`.
- So `g` maps `1` rigidly onto itself, which makes it the identity there. It permutes `{00, 01}`, so
  `g in <a>`.

**4.**
- **Amalgam.** `G0` is the pushout of `S4 <- <a | a^2> -> S3`. Both maps are injective, so `G0` is
  the amalgamated free product with the displayed presentation.
- **Onto.** `a, b, c` generate `V` (Bleak--Quick Theorem 2.1, in
  `bleak-quick-finite-presentations-of-thompson-v`). The relations of `G0` hold in `V` by 1 and 2,
  so the map is defined and onto.
- **Kernel.**
  - By (2.4), `V = <a, b, c | R>` with `R = {a^2, b^3, (ab)^4, c^-1(ac)^2 a, r5, r6, r7, r8}`.
  - `c^2` and `(ac)^3` are trivial in `V`, so adding them leaves the normal closure unchanged.
  - Modulo `c^2`, the word `c^-1 (ac)^2 a` equals `(ca)^3 = c^-1 (ac)^3 c`, so it is redundant once
    `(ac)^3` is a relator.
  - Hence `V = <a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3, r5, r6, r7, r8> = G0 / <<r5, r6, r7, r8>>`. ∎
