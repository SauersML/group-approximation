---
rg: 2
id: thompson-t-triangle-gap-via-classical-adjoint-trichotomy
kind: route
title: Reduce the relator gap on honest Delta(4,3,5)-representations to three gaps for dense homomorphisms of Delta into PSU(k), Inn(so(k)) and Sp(k)/{+-1}, after killing every finite-quotient, induced and fixed-group model at 1/2
target: thompson-t-triangle-genuine-rep-relator-gap
requires: [thompson-t-witnesses-are-dense-in-simple-adjoint-groups, thompson-t-triangle-gap-on-dense-projective-unitary-images, thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images, thompson-t-triangle-gap-on-dense-symplectic-adjoint-images]
---

*Distinct from* `thompson-t-not-mf-via-classical-adjoint-trichotomy`, which splits the flagship over
`Z/4 * Z/3`. This route splits (R_Delta) over the triangle group, where the pentagon relator is exact.
Each hole here is implied by the matching hole there.


**The route.** Let `eps` be the minimum of the constants of the three Delta-level gap claims.
- Suppose (R_Delta) failed: there are nontrivial irreducible representations `sigma_n` of `Delta` with
  `d_T(sigma_n) -> 0`.
- `Delta` is perfect, so `eta_0 = 1/2`. For large `n`, item 4 of
  `thompson-t-witnesses-are-dense-in-simple-adjoint-groups` and the corollary of
  `lie-closure-trichotomy-without-finite-quotients` give a dense `tau_n : Delta -> Inn(X(k))` with
  `k` large and defect `<= 2 d_T(sigma_n) < eps`.
- This contradicts `Gap_Delta(X)`.

**Each hole is necessary.** By item 2 of the parent claim, (R_Delta) implies each of the three gaps.

**Model classes that are already dead** (item 5 of the parent claim), uniformly in dimension:
- anything through a finite quotient of `Delta`, at `1/2`;
- anything induced from a finite-index (for example, surface) subgroup, at `sqrt 2`;
- anything pulled back from one fixed compact group, such as the `Sym^m` towers over a dense
  `Delta -> SO(3)`, at `min(1/2, gamma_(dim M)/2)`.

A refutation of (R_Delta) must be a sequence of dense homomorphisms of `Delta` into a classical
adjoint group of rank tending to infinity, on which `r_1` and `r_2` tend to `1`.
