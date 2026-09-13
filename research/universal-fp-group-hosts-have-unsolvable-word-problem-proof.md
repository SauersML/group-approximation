---
rg: 2
id: universal-fp-group-hosts-have-unsolvable-word-problem-proof
kind: route
title: "Proof that hosts of a universal finitely presented group have unsolvable word problem, infinite cd and all finite subgroups"
target: universal-fp-group-hosts-have-unsolvable-word-problem
requires: []
---

Let `U ≤ H` with `U` universal finitely presented.

1. **Word problem.** There is a finitely presented group `B` with unsolvable
   word problem (Novikov 1955, Boone 1958). `B` embeds in `U ≤ H`. A finitely
   generated subgroup of a finitely generated group with solvable word
   problem has solvable word problem: write each generator of the subgroup as
   a word in the generators of the ambient group, rewrite the input word, and
   run the ambient algorithm. So if `H` is finitely generated, its word
   problem is unsolvable.
2. **Cohomological dimension.** `Z^k` is finitely presented, so `Z^k ≤ U ≤ H`
   for every `k`. Cohomological dimension over a ring `R` is monotone under
   passage to subgroups, and `cd_R(Z^k) = k` for every nonzero commutative `R`
   (`H^k(Z^k; R) = R`, from the `k`-torus). So `cd_R(H) ≥ k` for all `k`. A
   group of type `FP` over `R` has a finite-length resolution of `R` by
   finitely generated projective `RH`-modules, so `cd_R(H) < ∞`; hence `H` is
   not of type `FP` over `R`. A group of finite
   virtual cohomological dimension `d` contains no `Z^k` with `k > d`: a
   torsion-free finite-index subgroup `H_0` has `cd = d`, and `Z^k ∩ H_0` has
   finite index in `Z^k`, so it is free abelian of rank `k` with `cd ≤ d`.
3. **Torsion.** Every finite group is finitely presented, so it embeds in `U`.

**Solvable-word-problem families.** Finitely generated linear groups have
solvable word problem, because they embed in `GL_n` of a finitely generated
field, where equality is decidable. Finitely presented residually finite
groups have solvable word problem (McKinsey 1943, Mal'cev, Mostowski 1966).
Hyperbolic and automatic groups have solvable word problem: Dehn's algorithm
for the first; the fellow-traveller normal forms of Epstein et al., *Word
Processing in Groups* (1992), for the second. Groups acting properly and
cocompactly on CAT(0) spaces are finitely presented with quadratic Dehn
function (Bridson--Haefliger, *Metric spaces of non-positive curvature*,
Part III.Γ), so their word problem is solvable.
Mapping class groups, `Aut(F_n)` and `Out(F_n)` are finitely presented and
residually finite. `F`, `T`, `V` and `nV` have solvable word problem, since
their elements are finite piecewise-affine data on the Cantor set or cube and
equality of such maps is decidable. Item 1 then excludes each family as a
host of `U`.
