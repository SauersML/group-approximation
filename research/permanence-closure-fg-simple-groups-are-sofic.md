---
rg: 2
id: permanence-closure-fg-simple-groups-are-sofic
kind: claim
title: Every finitely generated simple group in the surjunctivity permanence closure is sofic
distinct_from:
  permanence-closure-contains-fg-simple-nonsofic-group: that asks for a finitely generated simple nonsofic group in S*; this proves there is none, which refutes it.
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that excludes finitely presented simple nonsofic subgroups by a stage induction that breaks at local embeddings; this uses an invariant closed under all seven operations, including O3, and needs no finite presentation.
  fg-simple-subgroups-of-local-embedding-free-closure-are-sofic: that treats the closure without O3; this covers the full closure S*.
artifacts:
  - research/artifacts/sofic-indicable-closure-2026-09-17.md
---

**ESTABLISHED** by `permanence-closure-fg-simple-groups-are-sofic-proof`.

**The invariant.** Call a group `H` *locally sofic-indicable* (`H in LSI`) if every nontrivial finitely generated
subgroup of `H` has a nontrivial sofic quotient.

**Theorem.** Let `S*` be the closure of `gottschalk-counterexamples-lie-outside-the-permanence-closure`. Then
`S* ⊆ LSI`.

**Corollaries.**
1. Every finitely generated simple group in `S*` is sofic. Its only nontrivial quotient is itself.
2. `permanence-closure-contains-fg-simple-nonsofic-group` is false.
3. *General evasion.* A group that contains a nontrivial finitely generated subgroup with no nontrivial sofic
   quotient lies outside `S*`. Finitely presented simple nonsofic groups are one case, so this contains the evasion
   theorem of `gottschalk-counterexamples-lie-outside-the-permanence-closure`.
4. If `A(Y)` is finitely generated and simple
   (`kun-thom-product-action-alternating-full-group-is-fg-simple`), then `A(Y)` is not locally embeddable into `S*`,
   since it is nonsofic (`kun-thom-product-action-alternating-full-group-is-nonsofic`). So
   `kun-thom-full-group-balls-embed-in-permanence-closure` fails in that case.

**What the obstruction kills.** Any enlargement of `S*` by further operations of these two kinds adds no finitely
generated simple nonsofic group:
- extensions whose kernel lies in `LSI`;
- local-embedding or limit operations.
Gottschalk's conjecture reduces to finitely generated simple groups (`finitely-generated-simple-groups-are-surjunctive`),
so no permanence scheme of this shape decides a single nonsofic case of the reduced problem.

**What escapes.** The following are not of that shape:
- surjunctivity theorems for amalgams or HNN extensions with no fold that is injective on vertex groups
  (Burger--Mozes type lattices);
- permanence for topological full groups themselves;
- direct proofs for a specific simple group.

**Calibration.** Artifact Section 5.
- Sofic simple groups lie in `LSI`.
- The nonsofic Kun--Thom wreath lies in `LSI`, as it must, since it is in `S*`.
- The binary Leavitt unit group lies outside `LSI`, which agrees with the landed evasion result.
