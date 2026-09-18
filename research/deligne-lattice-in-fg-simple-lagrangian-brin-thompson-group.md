---
rg: 2
id: deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group
kind: claim
title: For every n >= 2 Deligne's lattice embeds in the finitely generated simple commutator subgroup of the Lagrangian Brin-Thompson group [[(Sp_2n(Z) on the unimodular Maslov Cantorization) x Cuntz]]; for n = 1 this group is 2V and the embedded lattice is B_3
distinct_from:
  lagrangian-thompson-group-contains-deligne-lattice: that embeds Γ̃ in V_Λ^τ for odd n >= 3 and claims nothing on simplicity or finite generation; this covers every n >= 2, including the Sp_4 case of deligne-lattice-satisfies-boone-higman, replaces the odometer groupoid by the Cuntz groupoid, and puts Γ̃ inside a commutator subgroup that is simple and finitely generated.
  lagrangian-thompson-group-is-finitely-presented: that is the open question (finite presentation, simplicity, containment) for V_Λ^τ at odd n; for the unimodular Brin-Thompson variant this settles simplicity and containment and adds finite generation, leaving finite presentation open in lagrangian-brin-thompson-group-is-finitely-presented.
  deligne-class-dies-on-some-rational-projective-host: that seeks a rational projective host 𝒯_m on which the class dies; this is a different host family, on the Lagrangian Grassmannian, where the class is already dead.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that puts a Kazhdan group in a full group of (M ⋊ Γ) × G_2 through its own faithful action; here the acting group is the residually finite Sp_2n(Z), and the non-residually-finite Γ̃ enters only through a Z-valued cocycle into V.
---

**ESTABLISHED.** Lane proof in `deligne-lattice-lagrangian-brin-thompson-embedding-proof`,
not reviewed. It uses:
- facts about Deligne's lattice from `deligne-universal-cover-lattice-is-non-rf-kazhdan`
  (cited there);
- the lift of `deligne-extension-dies-on-lagrangian-cantor-covers`;
- the imports `matui-purely-infinite-minimal-full-groups-have-simple-d` and
  `nekrashevych-symmetric-and-alternating-full-groups` (Theorems 4.1 and 5.6);
- `ample-groupoid-products-expansive-iff-factors-are`.

No priority is claimed.

## Definitions

- `Y_u` and `π : Y_u → Λ_n(R)` are as in
  `unimodular-maslov-cantorization-is-minimal-expansive`.
- `F_n` is a single point if `n` is odd. If `n` is even, it is `F_3^{2n} ∖ {0}`, with
  `Sp_{2n}(Z)` acting by reduction mod 3.
- `𝒢_n` is the groupoid of germs of `Sp_{2n}(Z)` acting on `Y_u × F_n`. The acting group
  is effectively `PSp_{2n}(Z)` for odd `n` and `Sp_{2n}(Z)` for even `n`. Those actions
  are faithful and topologically free, so `𝒢_n` is their action groupoid.
- `G_2` is the Cuntz groupoid on `C = {0,1}^N`, with `[[G_2]] = V`.
- The **Lagrangian Brin–Thompson group** is `2V_Λ(n) = [[𝒢_n × G_2]]`, acting on
  `Y_u × F_n × C`.
  - Its elements are the homeomorphisms that agree, on each piece of some finite clopen
    partition, with a pair `(γ, g)` where `γ ∈ Sp_{2n}(Z)` and `g ∈ V`.
- `Γ̃_n` is Deligne's lattice, the preimage of `Sp_{2n}(Z)` in the universal cover of
  `Sp_{2n}(R)`.

## Statement

1. **The host.** `D(2V_Λ(n))` is simple and finitely generated. It equals Nekrashevych's
   alternating group `A(𝒢_n × G_2)`, and it has solvable word problem.
2. **The embedding.** For every `n ≥ 2`, `Γ̃_n` embeds in `D(2V_Λ(n))`.
   - The central subgroup `ker(Γ̃_n → Sp_{2n}(Z)) = ⟨z⟩` acts only on the `C` coordinate.
   - It acts there through an infinite cyclic subgroup of `V`.
3. **The case n = 1.**
   - `Y_u` is the Farey Cantor set and `𝒢_1 × G_2 ≅ G_2 × G_2`, so `2V_Λ(1) ≅ 2V`.
   - `2V` is simple and finitely presented (Brin; textbook, not read at source).
   - The construction of item 2 embeds `Γ̃_1 = B_3` in `2V`. Here `B_3` is the preimage
     of `SL_2(Z)` in the universal cover of `SL_2(R)`.
4. **Not almost-V.** By `deligne-lift-actions-are-not-almost-v`, these actions are not
   almost-V. So Belk–Hyde–Matucci Theorem 2.1 over `V` cannot certify finite
   presentation of `2V_Λ(n)`.

## What this does and does not give

- **Not new in itself.** Embedding `Γ̃_n` in *some* finitely generated simple group with
  solvable word problem is classical (Boone–Higman and Thompson; not read at source). It
  also follows from the same argument with `Γ̃_n` acting on its own free subshift.
- **The content is the host.**
  - Its groupoid is built from the linear, residually finite group `Sp_{2n}(Z)` acting on
    a Cantorized real algebraic variety, times the Cuntz groupoid.
  - `Γ̃_n` enters only through the Maslov cocycle.
  - At `n = 1` the host is exactly `2V`, which is finitely presented.
- **What remains.** Boone–Higman for `Γ̃_n` now follows from finite presentation of one
  explicit group, whose definition does not mention `Γ̃_n`. This is
  `lagrangian-brin-thompson-group-is-finitely-presented`, used in the route
  `deligne-lattice-bh-via-lagrangian-brin-thompson-group`.
- **Not claimed.** Finite presentation.
- **Robustness.** The simplicity part of item 1, and item 2, also hold with `Y_Λ` of
  `lagrangian-thompson-group-contains-deligne-lattice` in place of `Y_u`, by item 8 of
  the Cantorization node. Finite generation there would need expansivity of `Y_Λ`, which
  is not known.
