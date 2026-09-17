---
rg: 2
id: a2-action-kernels-are-recursive
kind: claim
title: Every type [A_2] action has a recursive kernel, so every action image has solvable word problem
refuted_by:
  - some-a2-action-has-a-nonrecursive-kernel
distinct_from:
  a2-kernel-removal-forces-recursive-kernel: that proves every type [A_2] kernel is co-recursively enumerable and every removable kernel is recursive; this asserts that every kernel is recursive.
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that asks for removal of every kernel, which implies this; this is only the computability condition, which gives removal once the permutational Boone--Higman conjecture is added.
  a2-kernel-removal-iff-image-satisfies-pbh: that proves removal of one kernel is the permutational conclusion for the image; this is the computability hypothesis under which that conclusion would follow from the permutational conjecture.
---

**OPEN.**

**Statement.** Let `G ↷ S` be of type [A_2], in the sense of
Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Definition 1.3:
- `G` is finitely presented;
- point stabilizers are finitely generated;
- there are finitely many orbits on `S x S`.

Let `K` be its kernel. Then the set of words in a finite generating set of `G`
representing elements of `K` is recursive. Equivalently, the action image `G/K`
has solvable word problem.

**What is known.**
- **Co-r.e.** `K` is always co-recursively enumerable
  (`a2-kernel-removal-forces-recursive-kernel`, part (a)). So `K` is recursive
  iff it is r.e., iff `G/K` is recursively presented.
- **Necessary for Question 5.9.** A removable kernel is recursive (same node,
  part (b)). A positive first part of FFWZ Question 5.9 therefore implies this
  claim.
- **Sufficient modulo PBH.** This claim, `permutational-boone-higman-conjecture`
  and `a2-kernel-removal-iff-image-satisfies-pbh` together give the first part
  of Question 5.9 (route `a2-kernel-removal-via-pbh-and-recursive-kernels`).
  Under PBH, the first part of Question 5.9 is exactly this claim.
- **Faithful actions give nothing.** A type (A_2) action has trivial kernel.

**Where a counterexample would come from.** Take the FFWZ Theorem C actor of an
infinite finitely presented simple group `Γ`. Its one-variable mixed identities
many-one reduce to its kernel (`a2-kernel-removal-forces-recursive-kernel`, part
(c)). So a finitely presented simple group with a non-recursive set of mixed
identities would refute this claim. No such group is known in this graph.

**Status of the question.** FFWZ do not ask it, and no literature search beyond
the FFWZ text was made.

## Attempts

**Attempt 1 (2026-09-17, swarm-0917, inverter): biography of a minimal
counterexample.** Assume `G ↷ S` of type `[A_2]` has a non-recursive kernel `K`. It
is forced to have the following properties. Each comes from an established node or
is proved here.

- **It may be taken transitive (proved here).**
  - There are finitely many orbits `S_1, ..., S_p`, since the diagonal of `S x S`
    meets finitely many orbits.
  - Each restriction `G ↷ S_i` is of type `[A_2]`: it has the same group, the same
    stabilizers and a subset of the pair orbits.
  - Its kernel `K_i` is co-r.e. (`a2-kernel-removal-forces-recursive-kernel` (a)),
    and `K = K_1 ∩ ... ∩ K_p`.
  - If every `K_i` were r.e., then `K` would be r.e., hence recursive. So some
    transitive restriction is again a counterexample.
  - Hence `S = G/P` with `P` finitely generated and `|P \ G / P| < ∞`.
- **Image and stabilizer images.** `G/K` is not recursively presented. Every
  point-stabilizer image is finitely generated but not finitely presented
  (`a2-stabilizer-image-presentation-controls-kernel` (3)).
- **Sharp subgroups are decidable.** Every finitely generated `Γ <= G` with
  `Γ ∩ K = 1` has solvable word problem (same node, (4)).
- **No orbit-finite certificates.** This is
  `a2-kernel-recursion-ascends-normal-orbit-finite-chains` (5):
  - no finitely generated orbit-finite subgroup that starts a finitely generated
    normal chain up to `G` meets `K` in an r.e. set;
  - for any finite family of finitely generated orbit-finite subgroups, some element
    of `K` centralizes no conjugate of any member.
- **The cover is not free (proved here).** Let `F` be free of finite rank and
  `P <= F` finitely generated of infinite index.
  - If `P = 1`, the action is regular and has infinitely many pair orbits.
  - Otherwise, by M. Hall's theorem, `P` is a free factor of a finite-index subgroup
    `F' = P * C` with `C ≠ 1`.
  - Take a reduced alternating word `x` that starts and ends with a syllable in `C`.
    Every element `p x p'` with `p, p' in P` has normal form `p·x·p'`. So distinct
    such `x` lie in distinct double cosets `PxP`, and those sets do not change on
    passing from `F'` to `F`. There are infinitely many of them.
  - So every type `[A_2]` action of a free group has only finite orbits, and its
    kernel has finite index.

**Descent to the stabilizer, and where it stops (proved here).** Take a transitive
counterexample.
- **Setup.** Let `y_1, ..., y_q` represent the `P`-orbits on `S`, and put
  `M = Stab(y_1) ∩ ... ∩ Stab(y_q)`.
- **The kernel is a core.** An element `g in P` fixes every point iff `p^-1 g p in M`
  for all `p in P`. So `K = core_P(M)`, the kernel of `P ↷ S`.
- **The descent repeats the setting.** When `G` has finitely many orbits on `S^3`
  and two-point stabilizers are finitely generated, `P ↷ S` again has finitely many
  pair orbits and finitely generated stabilizers.
- **Where it stops.** `P` need not be finitely presented, and finite presentation is
  what makes the kernel co-r.e. and drives the certificate principle.

**No condition on tuple orbits suffices.** No hypothesis on the orbits of `k`-tuples
alone can prove this claim unless it also decides the one-variable mixed identities
of every infinite finitely presented simple group:
- the Theorem C actor of such a group is highly transitive
  (`relative-automorphism-action-is-highly-transitive`, as used in
  `a2-kernel-removal-recursive-kernel-proof` (c));
- its mixed identities many-one reduce to its kernel
  (`a2-kernel-removal-forces-recursive-kernel` (c)).

**Attempt 2 (2026-09-17, swarm-0917): recursively presented and lamp covers
(deaths at sketch level).**
- **Covers with a recursively presented image.** If a construction presents `G/K`
  recursively, then `K` is r.e., hence recursive. This kills every cover built as a
  quotient with an explicit r.e. kernel, e.g. elementary-group covers over
  recursively presented rings.
- **Lamp covers.** The lamp construction `C(C, B) x| V`, over a group `B` with a
  finite bi-index subgroup `B_0`, has kernel `C(C, core_B(B_0))` (sketch level). So it
  only transports the question to the pair `(B, B_0)`, which is the same problem. Not
  written as a node.

**Attempt 3 (2026-09-17, swarm-0917, inverter): permutation HNN realizations over
stabilizer edge groups (class killed under a uniformity hypothesis).** The natural
counterexample source is `permutation-hnn-realization-of-type-a-actor-is-a2`: its
kernel is recursive iff `<Γ, π>` has solvable word problem.
- **Centralizer test dies.** With identity edge map over a finitely generated finite
  bi-index subgroup `D`, the subgroup `C_Γ(π)` contains `D`, so it is a finite union of
  `D`-double cosets and is recursive
  (`overgroups-of-finite-bi-index-subgroups-are-recursive`). An inner edge map reduces
  to the identity case.
- **Tuple-stabilizer edge groups die under UTS.** If the edge groups are pointwise
  stabilizers of finite tuples and the actor has uniformly computable orbit-covering
  generating data for tuple stabilizers, then the kernel is recursive
  (`tuple-stabilizer-hnn-realizations-have-recursive-kernels`).
  - By Britton's lemma, every kernel element `k` satisfies
    `Γ ∩ k^-1 Γ k = Stab_Γ(T_k)` for an explicit tuple `T_k`, and it commutes with that
    stabilizer.
- **Where it dies.** A counterexample of this shape needs one of:
  - an actor in which some tuple stabilizer has infinitely many orbits;
  - an actor whose tuple-stabilizer data are not uniformly computable;
  - edge groups that are not tuple stabilizers.
