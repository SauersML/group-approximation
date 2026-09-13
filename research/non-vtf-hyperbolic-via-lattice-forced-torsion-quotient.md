---
rg: 2
id: non-vtf-hyperbolic-via-lattice-forced-torsion-quotient
kind: route
title: Force torsion invisible through a simple lattice in a product of trees, then pass to a hyperbolic quotient
target: non-virtually-torsion-free-hyperbolic-group
requires: []
---

The attack:
- Start from a CAT(0) group whose prime-order torsion is invisible because it lies in
  the normal closure of a quotientless subgroup. The model is a torsion-free simple
  lattice `Γ` in a product of trees, a Burger–Mozes group or one of Wise's complete
  square complex groups, amalgamated as `Γ *_{h=t} (Z/p x| Z)`.
- Make the group hyperbolic by a quotient that kills the flats while keeping the torsion
  alive: small cancellation, Dehn filling, or random relators.
- Invisibility passes to quotients automatically, because the image of `R_f` lies in
  `R_f`.

**Dead.** By `lattice-forced-torsion-dies-in-hyperbolic-quotients`, item 2, every
homomorphism to a word-hyperbolic group kills a simple subgroup containing `Z^2`, and
with it the forced torsion. By item 3, replacing the lattice by any quotientless
subgroup that could survive requires the hyperbolic quotient to be non-residually
finite already. So the attack has no content beyond the root.

**What survives.** The non-hyperbolic amalgam itself. It is a clean non-virtually
torsion-free CAT(0) group, with persistent Chern–Quillen classes
(`vtf-iff-chern-quillen-class-dies-on-finite-index`), and it serves as a calibration
object.
