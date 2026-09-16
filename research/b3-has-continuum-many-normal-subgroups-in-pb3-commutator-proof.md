---
rg: 2
id: b3-has-continuum-many-normal-subgroups-in-pb3-commutator-proof
kind: route
title: The relative multiplier of PB_3 is the Schur multiplier of the free metabelian group, of infinite rank, and S_3 is finite
target: b3-has-continuum-many-normal-subgroups-in-pb3-commutator
requires: []
artifacts:
  - research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md
---

Artifact §3–§4 (Lemma B and Corollary C).

1. **Splitting `PB_3`.** By Artin combing, `PB_3 = F × <Delta^2>`, where `F = ker(pi_{{1,2}})` is free on
   `A_13, A_23` and `Delta^2` is central. Hence `PB_3'' = F''` and `[PB_3, PB_3''] = [F, F'']`.
2. **Hopf's formula.** `Q_2 = F'' / [F, F''] ≅ H_2(M_2)`, where `M_2 = F/F''` is the free metabelian group of
   rank 2.
3. **The module `A`.** `A = F'/F'' = H_1` of the square-grid Cayley graph of `Gamma = Z^2`. It is isomorphic to
   `C_2` of the square tiling of `R^2`, which is the free module `Z Gamma`.
4. **LHS spectral sequence.** For `A -> M_2 -> Gamma`, `E_{2,1} = H_2(Gamma; Z Gamma) = 0` and
   `E_{3,0} = H_3(Z^2) = 0`. So `H_2(A)_Gamma = E^inf_{0,2}` embeds in `H_2(M_2)`.
5. **Coinvariants.** `H_2(A) = Λ^2 A`. `Gamma` acts freely on 2-subsets of `Gamma`, since `2t = 0` forces `t = 0`.
   So `Λ^2 A` is free over `Z Gamma` on `(Z^2 \ 0)/±`, and its coinvariants are `Z^(aleph_0)`. Hence `Q_2` is
   countable and not finitely generated, and `Q_2 ⊗ Q` has dimension `aleph_0`.
6. **Normal subgroups as submodules.** `B_3` acts on `Q_2` through `S_3`, since `PB_3` acts trivially. Normal
   subgroups of `B_3` between `[PB_3, PB_3'']` and `PB_3''` are exactly the preimages of `S_3`-invariant
   subgroups of `Q_2`.
7. **Chain.** Each finitely generated `Z[S_3]`-submodule is finitely generated as an abelian group, so it is
   proper. Adding one new element at a time gives an infinite strictly ascending chain.
8. **Continuum.** `Q_2 ⊗ Q` is an infinite direct sum of simple `Q[S_3]`-modules (Maschke). The preimages in
   `Q_2` of the `2^aleph_0` partial direct sums are pairwise distinct `S_3`-invariant subgroups.
