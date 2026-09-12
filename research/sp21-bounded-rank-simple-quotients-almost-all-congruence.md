---
rg: 2
id: sp21-bounded-rank-simple-quotients-almost-all-congruence
kind: claim
title: Bounded-rank simple quotients of a cocompact arithmetic Sp(n,1) lattice are congruence with finitely many exceptions
distinct_from:
  sp21-lattice-has-congruence-subgroup-property: that is the open claim that essentially every finite quotient is congruence; this proves it for simple quotients of Lie type of bounded rank, up to finitely many exceptions for each rank bound, and says nothing about alternating quotients, unbounded rank, or non-simple quotients
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that bounds the congruence quotients of a proper quotient; this bounds its non-congruence bounded-rank simple quotients
  sp21-lattice-positive-characteristic-images-finite: that excludes infinite linear images in characteristic p; this uses it, together with characteristic-zero superrigidity, to classify families of finite simple images
---

**ESTABLISHED.** Setting:
- `k` is a number field with ring of integers `O`;
- `G` is a simply connected absolutely almost simple `k`-group;
- `G(k_v)` is `Sp(n,1)` (`n >= 2`) or `F_4^(-20)` at one archimedean place `v`, and
  compact at the other archimedean places;
- `Γ <= G(O)` has finite index.

Fix `r >= 1`. Then only finitely many normal subgroups `N ⊴ Γ` satisfy both:
- `Γ/N` is a finite simple group of Lie type (twisted or not) of Lie rank at most `r`;
- `N` contains no principal congruence subgroup `Γ ∩ G(O, 𝔞)`, `𝔞 != 0`.

**Consequence for fillings.** For every `1 != M ⊴ Γ` and every `r`, the quotient
`Γ/M` has only finitely many simple quotients of Lie type of rank at most `r`.
- The congruence ones factor through the finite group `Γ̄/closure(M)`, by
  `normal-subgroups-of-arithmetic-lattices-are-congruence-open`.
- The others are among the finitely many exceptions above.

So the infinite families among the finite simple quotients of any one-element
filling `Γ/<<g^n>>` can only be:
- alternating groups;
- classical groups of unbounded rank.

`filling-no-finite-quotient-iff-simple-image-orders` then says which members
must be excluded.

Proof in `sp21-bounded-rank-simple-quotients-almost-all-congruence-proof`:
- an ultraproduct of the quotients, of characteristic `0` by
  `sp21-lattice-positive-characteristic-images-finite`;
- Zariski density;
- Margulis-form superrigidity (Corlette, Gromov--Schoen), which makes the
  ultraproduct representation a Galois conjugate of the inclusion;
- Łoś, which reads congruence off along the ultrafilter.

This is a standard style of argument, and no novelty is claimed. Not Lean-verified.
