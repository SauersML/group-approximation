---
rg: 2
id: bs-class-with-faithful-member-lies-in-type-a-class
kind: claim
title: If the generalized Baumslag--Solitar class over a finitely presented group has one faithful member, the whole class lies in the permutational Boone--Higman class
distinct_from:
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports Bux--Llosa Isenrich--Wu Theorem C with its plain conclusion, an embedding in a finitely presented simple group; this is the permutational conclusion, membership in B_A, read off from the same proof.
  free-generalized-bs-groups-have-type-a-overgroups: that imports the authors' Remark 12.7, the permutational statement for G = F_k only; this is the statement for every finitely presented G with a faithful member.
  faithful-finite-index-graphs-of-groups-have-type-a-overgroups: that needs the given graph of groups to act faithfully on its own Bass--Serre tree; this removes the faithfulness hypothesis on the input by the authors' gluing enlargement.
---

**ESTABLISHED** through `bs-class-faithful-member-type-a-proof` (lane proof, a
reading of a literature proof; not independently reviewed; no priority claimed).

**Setting.** For a group `G`, `BS_G` is the class of fundamental groups of finite
graphs of groups all of whose vertex and edge groups are abstractly commensurable
with `G`, with every edge inclusion of finite index (Bux--Llosa Isenrich--Wu,
arXiv:2408.05673v2, §11, as quoted in `free-generalized-bs-groups-have-type-a-overgroups`).
`B_A` is the class of `boone-higman-type-a-class-closed-under-finite-extensions`.

**Statement.** Let `G` be finitely presented. Suppose some nontrivial `H ∈ BS_G`
acts faithfully on its Bass--Serre tree. Then `BS_G ⊆ B_A`. In particular every
subgroup of every group in `BS_G` embeds in a finitely presented simple group, and
the class is closed under the permanence of `B_A` (finite direct products,
finite-index overgroups, free products).

**Known faithful members** (so the conclusion holds for `BS_G`):
- `G` torsion-free strongly scale-invariant, e.g. `Z^n` and the Heisenberg groups
  (BLIW Theorem 12.1: the ascending HNN extension along the scaling endomorphism);
- `G = F_k`, `k >= 2` (BLIW Theorem 12.5 / Remark 12.7);
- `G` a torsion-free finite-index subgroup of `SL_n(Z)`, `n >= 3`, or of a definite
  quaternion S-arithmetic group over two primes: `arithmetic-nsp-lattices-have-faithful-bs-members`.
