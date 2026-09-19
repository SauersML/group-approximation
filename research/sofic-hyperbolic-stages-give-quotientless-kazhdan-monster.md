---
rg: 2
id: sofic-hyperbolic-stages-give-quotientless-kazhdan-monster
kind: claim
title: The torsion-free Kazhdan Tarski monster has no proper finite-index subgroup and is sofic once its hyperbolic stages are, so a torsion-free sofic quotientless Kazhdan group exists unless a nonsofic hyperbolic group does
distinct_from:
  kazhdan-torsion-free-tarski-monster-satisfies-kk: that constructs the monster and proves Kadison--Kaplansky for it; this proves the monster has no finite quotient and inherits soficity from its stages, which gives a summit-hard lower bound for the torsion-free sofic quotientless Kazhdan gate.
  lef-kazhdan-group-without-finite-quotients-exists: that is an unconditional LEF quotientless Kazhdan group, but EL_3 over a unital ring always has Weyl torsion; this is torsion-free and conditional on the soficity of torsion-free hyperbolic Kazhdan groups.
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that reduces the flagship to one fixed hyperbolic host; this reads the same host question off a different target, the existence of a torsion-free sofic quotientless Kazhdan group.
  kazhdan-hyperbolic-group-without-finite-quotients: that asks for a hyperbolic quotientless Kazhdan group, equivalent to Gromov's question; this group is quotientless unconditionally but is not hyperbolic, and its open clause is soficity rather than finite quotients.
---

**ESTABLISHED** through `sofic-hyperbolic-stages-give-quotientless-kazhdan-monster-proof`.

Let `Gamma` be a torsion-free cocompact lattice in `Sp(n,1)`, `n >= 2`. Let `Q` be the
Olshanskii--Osin--Sapir torsion-free Tarski monster quotient of `Gamma` from
`kazhdan-torsion-free-tarski-monster-satisfies-kk`. It is the direct limit of torsion-free
hyperbolic quotients `Gamma = G(0) -> G(1) -> G(2) -> ...`.

**Theorem.**

1. (Unconditional.) `Q` is infinite, finitely generated, torsion-free and Kazhdan. It has **no
   proper subgroup of finite index**, so in particular no nontrivial finite quotient.
2. (Transfer.) If every stage `G(i)` is sofic, then `Q` is sofic. Each `G(i)` is a torsion-free
   hyperbolic Kazhdan group, being a quotient of `Gamma`.
3. (Dichotomy.) At least one of the following holds:
   - (SQK) there is an infinite, finitely generated, torsion-free, sofic Kazhdan group with no
     nontrivial finite quotient (`torsion-free-sofic-quotientless-kazhdan-group-exists`);
   - (NSH) some torsion-free hyperbolic Kazhdan quotient of `Gamma` is not sofic, so
     `nonsofic-hyperbolic-group` holds.

**Consequence for the torsion-free exact-radical goal.** Every witness of
`torsion-free-sofic-exact-mf-radical-over-z` has a kernel satisfying (SQK). This is recorded in
`torsion-free-sofic-quotientless-kazhdan-group-exists`. So (SQK) is a necessary gate of the goal
and of all three of its live routes. By item 3, a proof that the gate fails is a proof of the
flagship root `nonsofic-hyperbolic-group`. Every attempt to *refute* the goal through the
intrinsic properties that its kernel is forced to have is therefore at least summit-hard. Here
"intrinsic properties" means: sofic, torsion-free, Kazhdan, no finite quotient. Such a refutation
must use finite presentation of `G`, the exact radical, or the cyclic action.

**Not claimed.** The following are not claimed.
- That `Q` is MF, or that it is not MF.
- That `Rad_MF(Q semidirect Z) = Q` for any automorphism.
- That `Q` is finitely presented. As a non-hyperbolic lacunary hyperbolic group it is not expected
  to be, and that is not proved here.

So `Q` does not solve the goal, even conditionally.

Not Lean-verified. No literature survey for novelty was done beyond grep of this graph.
