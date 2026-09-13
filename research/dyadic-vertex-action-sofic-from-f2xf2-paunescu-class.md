---
rg: 2
id: dyadic-vertex-action-sofic-from-f2xf2-paunescu-class
kind: route
title: If every action of F2 x F2 is sofic, the measure equivalent lattice PSL2(Z[1/2]) has sofic frame dynamics, so its tree vertex action is sofic
target: dyadic-bruhat-tits-vertex-action-is-sofic
requires:
  - f2xf2-in-paunescu-class
  - paunescu-class-is-measure-equivalence-invariant
  - dyadic-vertex-soficity-equals-frame-dynamics-soficity
---

Put `H = PSL_2(R) × PSL_2(Q_2)`, `A = PSL_2(Z[1/2])`, `L = PSL_2(Q_2)`.

1. **Two lattices of one group.** `A`, embedded diagonally, is a non-uniform lattice in `H`
   (Borel--Harish-Chandra). Let `Γ(2) <= PSL_2(Z)` be the principal congruence subgroup, a free
   group of rank `2` and a lattice in `PSL_2(R)`. Let `Λ <= L` be a torsion-free cocompact lattice.
   `Λ` acts freely without inversions on the `3`-regular tree with finite quotient `X`, so
   `Λ ≅ π_1(X)` is free of rank `r = 1 + |V(X)|/2 >= 2`. Then `Γ(2) × Λ ≅ F_2 × F_r` is a lattice in
   `H`.
2. **Measure equivalence.** Two lattices of one lcsc group are measure equivalent (item 1 of
   `paunescu-class-is-measure-equivalence-invariant`). `F_2 × F_r` has finite index in `F_2 × F_2`,
   so the three groups `A`, `F_2 × F_r`, `F_2 × F_2` are measure equivalent.
3. **Membership.** `F_2 × F_2 ∈ 𝒮` (`f2xf2-in-paunescu-class`) and ME invariance give `A ∈ 𝒮`.
   So every p.m.p. action of `A` is sofic, in particular the frame dynamics `A ↷ (L/Λ, Haar)`.
4. **Vertex action.** Item 3 of `dyadic-vertex-soficity-equals-frame-dynamics-soficity` (p.m.p.
   soficity for one lattice) implies its item 1. That is the target: soficity of
   `A ↷ A/PSL_2(Z)`.

The same argument gives soficity of `PSL_2(Z[1/p]) ↷ PSL_2(Z[1/p])/PSL_2(Z)` for every prime `p`
from `F_2 × F_2 ∈ 𝒮`. That consequence uses the `p`-adic version of the equivalence, which is
not recorded here.
