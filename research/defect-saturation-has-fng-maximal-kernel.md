---
rg: 2
id: defect-saturation-has-fng-maximal-kernel
kind: claim
title: The defect-saturation group has a finitely normally generated maximal proper normal subgroup
distinct_from:
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that asks the same compactness question of the Chatterji-Kassabov normal-generator envelope, where the point of the quotient is to preserve an embedded simple core; this asks it of the defect-saturation group, where the point is to preserve the full MF radical, and no implication between the two is known in either direction.
  kazhdan-hyperbolic-continuum-non-fng-maximal-kernels: that exhibits one torsion-free hyperbolic Kazhdan group with continuum many maximal normal subgroups that are not finitely normally generated; this asks that one specific group have at least one that is, and the two statements are compatible.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general equivalence between finite presentability of a quotient and finite normal generation of its kernel; this asserts that one particular finitely presented group realizes the condition at a maximal kernel.
artifacts:
  - research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md
---

**OPEN.** Let `G` be the two-generated finitely presented torsion-free
property-`(T)` acylindrically hyperbolic group of
`defect-saturation-full-mf-radical`, so that every homomorphism from `G` to an
MF group is trivial. Then `G` has at least one maximal proper normal subgroup
`M` that is finitely normally generated in `G`.

By `fp-quotient-iff-kernel-finitely-normally-generated` this is equivalent to:
**some** maximal proper normal quotient of `G` is finitely presented. Since
maximality makes that quotient simple and
`defect-saturation-full-mf-radical` records that every nontrivial quotient of
`G` again has full MF residual, such a quotient witnesses
`fp-simple-full-mf-radical-group`. That deduction is the route
`fp-simple-full-mf-radical-from-fng-maximal-kernel`.

The quantifier is existential over the maximal normal subgroups of one
explicitly presented group, and over the freedom left in the defect-saturation
construction. It is therefore not a restatement of its consequence.

## Attempts

1. **Zorn's lemma restricted to the finitely normally generated proper
   normal subgroups.** *Dies on chains*, exactly as in the Chatterji--Kassabov
   lane: the union of an ascending chain of finitely normally generated normal
   subgroups need not be finitely normally generated, so the restricted poset
   has no upper bounds. Finite generation of `G` gives properness of the union
   and nothing more.
2. **Derive a Max-n condition from property (T).** *Dies as a general
   principle* at `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`.
   That obstruction is sharp for this lane rather than incidental: its witness
   is finitely presented, torsion-free, word-hyperbolic and Kazhdan, and `G`
   is finitely presented, torsion-free, acylindrically hyperbolic and Kazhdan,
   so no argument that uses only this adjective list can succeed. What is not
   excluded is that the specific routing quotient used to build `G` has one
   maximal kernel with a finite normal generating set.
3. **Iterate the routing quotient until it is maximal.** *Dies.* Every
   Hull--Osin small-cancellation quotient is again acylindrically hyperbolic,
   and acylindrically hyperbolic groups are SQ-universal, hence never simple.
   So no finite stage is a maximal quotient. A maximal kernel reached as the
   union of a strictly ascending chain `K_1 < K_2 < ...` is never finitely
   normally generated: finitely many normal generators would all lie in some
   `K_N`, forcing `K_N = K_(N+1)`. A finitely normally generated maximal kernel
   therefore has to come from a quotient map that is not a small-cancellation
   limit.

## Status of the payoff

The consequence this claim was built to deliver, `fp-simple-full-mf-radical-group`,
is now established independently by the binary Leavitt unit group
(`fp-simple-full-mf-radical-via-leavitt-unit-group`). This claim stays open as a
question about one group's normal lattice. If it holds, it would give a
*torsion-free* finitely presented simple group with full MF radical, provided
the simple quotient inherits torsion-freeness, which is not automatic. The
Leavitt witness has torsion.
