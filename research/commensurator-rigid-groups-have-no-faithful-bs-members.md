---
rg: 2
id: commensurator-rigid-groups-have-no-faithful-bs-members
kind: claim
title: If a group maps injectively onto a finite-index subgroup of its abstract commensurator, no generalized Baumslag--Solitar group over it acts faithfully on its Bass--Serre tree
distinct_from:
  bs-class-with-faithful-member-lies-in-type-a-class: that turns one faithful member of BS_G into B_A for the whole class; this shows that for commensurator-rigid G no faithful member exists, so that route and Bux--Llosa Isenrich--Wu Theorem C never apply to G or to any group commensurable with it.
  arithmetic-nsp-lattices-have-faithful-bs-members: that produces faithful members from a commensurator element with no power in the lattice, so from a large commensurator; this is the complementary statement, that a commensurator which is virtually the group itself leaves no faithful member.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports Theorem C with the authors' remark that residual finiteness is the only obstruction they know; this is a second obstruction, commensurator rigidity, which residually finite groups can have.
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that asks for a finitely presented residually finite group with no faithful regular-tree action, which would block faithful members through bounded composition factors; this blocks them through commensurations, for groups that do act on regular rooted trees.
---

**ESTABLISHED** by `commensurator-rigid-no-faithful-bs-member-proof` (lane proof,
elementary; not reviewed; no priority claimed). The two instances depend on cited
rigidity theorems that were not read at source this session.

**Setting.** `Comm(G)` is the abstract commensurator: isomorphisms between
finite-index subgroups of `G`, modulo agreement on a finite-index subgroup. `BS_G`
is the class of Bux--Llosa Isenrich--Wu (arXiv:2408.05673v2, §11): fundamental
groups of finite graphs of groups whose vertex and edge groups are abstractly
commensurable with `G`, with every edge inclusion of finite index.

**Theorem.** Let `G` be an infinite group such that the inner-automorphism map
`G -> Comm(G)` is injective and has image of finite index. Then no group in
`BS_G` acts faithfully on its Bass--Serre tree. More precisely, for every
`H ∈ BS_G` and every vertex group `G_v`, some finite-index subgroup of `G_v` acts
trivially on the tree.

**Consequences.**
1. Bux--Llosa Isenrich--Wu Theorem C, and its permutational form
   `bs-class-with-faithful-member-lies-in-type-a-class`, never apply to such `G`,
   or to any group commensurable with it. The hypothesis is invariant under
   commensurability, so this is a property of the commensurability class.
2. The authors write that residual finiteness is the only obstruction to Theorem C
   they are aware of. This is a second obstruction, and it bites for finitely
   presented residually finite groups.
3. **Instances** (cited rigidity theorems, not read at source):
   - `Out(F_n)`, `n >= 4`: Farb--Handel, *Commensurations of Out(F_n)*, Publ. Math.
     IHES 105 (2007), prove that `Out(F_n) -> Comm(Out(F_n))` is an isomorphism.
   - `Mod(S_g)`, closed, `g >= 3`: Ivanov's theorem identifies `Comm(Mod(S_g))`
     with the extended mapping class group, which contains `Mod(S_g)` with
     index 2.

   These are BBMZ Problem 5.3(3) and the open part of 5.3(2), and both groups are
   finitely presented and residually finite, so they also lie inside Problem
   5.3(12) (`fp-residually-finite-boone-higman`). The generalized
   Baumslag--Solitar mechanism cannot reach any of these items through these
   groups.
4. **Calibration.** Arithmetic lattices such as `SL_n(Z)`, `n >= 3`, have dense
   commensurators, so the hypothesis fails, and faithful members exist
   (`arithmetic-nsp-lattices-have-faithful-bs-members`). `Z^n` has commensurator
   `GL_n(Q)`, again not virtually `Z^n`, and faithful members exist (BLIW
   Theorem 12.1). So the theorem is consistent with every known faithful member.

**Scope.** The theorem says nothing about Theorem B (faithful cocompact actions on
locally finite trees by overgroups in which `G` is not a vertex group), nor about
other hosts. It only removes the generalized Baumslag--Solitar route.
