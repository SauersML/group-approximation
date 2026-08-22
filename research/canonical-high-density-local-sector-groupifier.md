---
rg: 2
id: canonical-high-density-local-sector-groupifier
kind: claim
title: Groupify one finite BCS on local sectors below the total Plancherel-deficit threshold
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for a literal homomorphism of the whole BCS algebra into one common corner; this permits different noncommuting local sectors and asks only for small total canonical codimension plus state-dependent local rows.
  common-partial-isometry-swap-game-compiler: that authenticates one common source partial isometry and all Gram rows on it; this asks the weaker geometric task of making the meet large by canonical density, after which no source word or partial isometry is needed.
  finite-product-selected-type-mark-does-not-align-carriers: that refutes inference of a meet from product moments; this explicitly requires a sum-of-codimensions bound which forces the meet in every finite matrix model.
---

OPEN.
For a fixed finite BCS game of finite-dimensional gap `Delta>0` and a perfect
commuting strategy, construct a finitely presented group `Gamma` with:

1. finite-subgroup algebra projections `q_c` whose canonical Plancherel
   masses `alpha_c` satisfy

   ```text
   sum_c(1-alpha_c)<Delta/(1+Delta);                         (CHD1)
   ```

2. group-word packets which, after exactifying those finite subgroups in a
   canonical matrix microstate, produce context PVMs, context involutions and
   Bob involutions with

   ```text
   ||F_cq_c||_2=o(1),
   ||(A_(c,x)-B_x)q_c||_2=o(1);                              (CHD2)
   ```

3. one exact representation realizing the perfect commuting strategy and
   keeping a specified group-algebra mark nonzero.

By `high-density-local-sectors-force-one-bcs-gram`, `(CHD1)--(CHD2)` exclude
canonical finite-dimensional microstates.  The exact marked representation
ensures the presentation is nontrivial, so the resulting group is
nonhyperlinear.

## Attempts

The common irreducible selected-type atlas does not meet `(CHD1)`: a central
type projection has canonical mass `dim(rho)^2/|K|`, and taking one private
type per context accumulates the complementary Plancherel masses rather than
the selected masses.  Tensoring the complete context packets can force a
large literal meet, but `tensor-context-types-classicalize-common-source`
then destroys the perfect nonclassical witness.  The live possibility is a
high-rank **accepting** sector (large sum of types, not one selected type)
whose rejected complement pays only the local verifier row while distinct
context algebras remain noncommuting in the exact infinite model.
