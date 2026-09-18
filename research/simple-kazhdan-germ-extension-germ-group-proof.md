---
rg: 2
id: simple-kazhdan-germ-extension-germ-group-proof
kind: route
title: Specialize the FW germ reduction to a simple input, rule out the V-local part by Haagerup, and read off finite presentation from the SingFix lemma
target: simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group
requires:
  - almost-v-fw-subgroups-act-through-finitely-many-germs
  - thompson-v-has-haagerup-property
  - bhm-singfix-condition-forces-fp-germ-groups
  - property-t-implies-property-fa
---

Notation as in the claim. `E` is a subgroup of `H = {g ∈ Homeo(C) : sing(g) finite}`
(`almost-v-fw-subgroups-act-through-finitely-many-germs`, Setting), and property (T)
implies FW.

1. **No finite-index step.** An infinite simple group has no proper finite-index
   subgroup: the core of one would be a proper normal subgroup of finite index. So the
   finite-index subgroup `Γ_0` of item 1 of the FW germ reduction is `S` itself. That
   item gives a finite set `F ⊂ C` fixed pointwise by `S`, an element `h ∈ H`, and the
   germ homomorphism `φ : S -> ∏_{y ∈ F} (S)_y` with `ker φ ⊆ h V h^-1`.
2. **The kernel is trivial.** `ker φ` is normal in `S`, so it is `1` or `S`. If it were
   `S`, then `h^-1 S h` would be an infinite Kazhdan subgroup of `V`. By
   `thompson-v-has-haagerup-property`, every Kazhdan subgroup of `V` is finite. So
   `ker φ = 1`. In particular `F ≠ ∅`: for `F = ∅` the product is trivial and
   `ker φ = S`.
3. **One coordinate is injective.** Each coordinate `φ_y : S -> (S)_y` has kernel `1` or
   `S`. If every kernel were `S`, then `φ` would be trivial, contradicting item 2. So
   some `φ_y` is injective, and `S ≅ φ_y(S) <= (E)_y`.
4. **The point is singular.** Suppose `y ∉ sing(E)`. Every `g ∈ Stab_E(y)` agrees near
   `y` with some `v ∈ V`, and then `v(y) = y`. So `(E)_y` lies in the germ group of
   `Stab_V(y)` at `y`. That group is abelian. Near `y`, `v` replaces a prefix `u` of `y`
   by a prefix `u'` of `y`, so `y = uz = u'z`. If `|u| = |u'|` then `u = u'` and the
   germ is trivial. If `|u| < |u'|`, both are prefixes of `y`, so `u' = ua` with `a`
   nonempty, and `uz = uaz` gives `z = az`, so `z = a^∞` and `y = u a^∞` is eventually
   periodic (the case `|u| > |u'|` is symmetric). The germ is then the shift of the
   periodic tail by a whole number of periods of the primitive root of `a`. So the
   germ group at `y` is trivial when `y` is not eventually periodic, and infinite
   cyclic when it is. Either way it is abelian, and an infinite simple group is
   non-abelian, so it cannot embed in `(E)_y`.
   Hence `y ∈ sing(E)`.
5. **Finite presentation.** Theorem 2.1 of Belk--Hyde--Matucci at `n = 2` asks that
   `SingFix_E({y},{y})` have type `F_2`, so it is finitely presented. By
   `bhm-singfix-condition-forces-fp-germ-groups`, item 3, `(E)_y` is then finitely
   presented. It contains the infinite Kazhdan group `S`, so it is not amenable, and by
   the standard fact used in `thompson-v-has-haagerup-property` it is not a-T-menable.
   `∎`
