---
rg: 2
id: bernoulli-factor-algebraic-actions-finite-stabilizers-proof
kind: route
title: One invariant character pulled back to a Bernoulli shift contradicts mixing along an infinite stabilizer
target: bernoulli-factor-algebraic-actions-have-finite-stabilizers
requires: []
---

Notation as in the target. Let `phi: L^G -> X_M` be a factor map and fix `a != 0` in `M`
with `H = Stab_G(a)`.

1. **An invariant unit vector.** Put `f_a(x) = x(a)`, a continuous character `X_M -> T`.
   Pontryagin duality makes `x ↦ x(a)` a nontrivial character when `a != 0`, so
   `∫ f_a dm_X = 0` and `‖f_a‖_2 = 1`. For `g` in `H`,

       (g.f_a)(x) = f_a(g^-1 . x) = (g^-1 . x)(a) = x(g a) = x(a) = f_a(x).

   So `f_a` is an `H`-invariant unit vector in `L²_0(X_M)`.
2. **Pull back.** `F = f_a ∘ phi` lies in `L²(L^G, lambda^G)`, has integral `0` and norm `1`
   because `phi` pushes `lambda^G` to `m_X`, and is `H`-invariant because `phi` is equivariant.
3. **Mixing along an infinite subgroup.** Let `f, f'` in `L²_0(L^G)` depend only on the
   coordinates in finite sets `S, S'`. If `h S ∩ S' = ∅`, then `h.f` and `f'` depend on disjoint
   coordinates, so `<h.f, f'> = (∫ f)(∫ conj f') = 0`. The set of `h` with `h S ∩ S' != ∅` is
   contained in the finite set `S' S^-1`. Such functions are dense in `L²_0`, and the maps
   `f ↦ h.f` are unitary, so `<h.f, f'> -> 0` as `h` leaves finite subsets of `G`, for all
   `f, f'` in `L²_0`.
4. **Conclusion.** `<h.F, F> = 1` for every `h` in `H`. If `H` were infinite, step 3 along `H`
   would give `1 -> 0`. So `H` is finite.

**The remarks in the target.**
- A nonzero `v = (v_1, ..., v_n)` in `F_p[G]^n` has finite support `S`, the union of the supports
  of its coordinates. If `g v = v`, then `g S = S`, and left multiplication is free, so the
  stabilizer has at most `|S|` elements.
- If `X × B ≅ B'`, the projection `X × B -> X` composed with the isomorphism is a factor map
  `B' -> X`.

The Leavitt application is proved in `leavitt-module-dual-actions-self-square-proof`.
