---
rg: 2
id: simple-lamp-one-relation-proof
kind: route
title: Simplicity at one site plus transitivity spreads the relation to every site
target: simple-lamp-radical-one-relation
requires: [compression-wreath-five-radicals-coincide]
artifacts:
  - GroupApproximation/Algebra/PermutationalWreathSimple.lean
---

## Why sufficient

The prerequisite, at a perfect lamp, gives `Rad_MF(W_S) = S^(G*/Gamma*)`, so
only the normal-generation statement is left.

Let `N` be the normal closure of `r` in `W_S`.  Since the lamp base is normal
and `r` lies in it, `N <= S^(G*/Gamma*)`.  Inside the site subgroup `S_{x_0}`,
the normal closure of the nonidentity `s` is a nontrivial normal subgroup of a
simple group, hence all of `S_{x_0}`; conjugation inside `S_{x_0}` is
conjugation inside `W_S`, so `S_{x_0} <= N`.  The action of `G*` on
`G*/Gamma*` is transitive, so every other site subgroup is a `W_S`-conjugate
of `S_{x_0}` and also lies in `N`.  The site subgroups generate the restricted
direct sum, so `N` is everything.

`PermutationalWreathSimple.lamp_le_normalClosure_single` is exactly this
argument at kernel level, resting on `Lamp.mem_closure_singles` (every
finitely supported configuration is a product of one-site configurations).

The quotient statement is then the first isomorphism theorem together with the
semidirect-product splitting, and the invisibility of the change is the
Hom-set bijection in the prerequisite.

For `S = A_5`, `(1 2)(3 4)` is a nonidentity involution of `A_5`, which is
simple; simplicity of `A_n` for `n >= 5` is proved from scratch in section
52.1 of the dossier (3-cycles generate, they are all conjugate under `A_n`,
and every nontrivial normal subgroup contains one).

Non-finite-generation of the radical: the cosets `t^n Gamma*` are pairwise
distinct because the height homomorphism separates them, so the site set is
infinite; any finite subset of `S^(X)` is supported on a finite union of
sites and generates a subgroup with the same finite support.
