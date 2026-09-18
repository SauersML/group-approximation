---
rg: 2
id: arithmetic-lie-lattices-have-faithful-bs-members
kind: claim
title: Every arithmetic lattice in a semisimple Lie group has a faithful Hecke member in its Baumslag--Solitar class, so the whole class lies in the permutational Boone--Higman class; this includes closed surface groups
distinct_from:
  arithmetic-nsp-lattices-have-faithful-bs-members: that uses the normal subgroup theorem and one commensurator letter, and covers SL_n(Z), n >= 3, and quaternion lattices on two trees; this needs no normal subgroup theorem, covers every arithmetic lattice in a connected semisimple Lie group, including rank one, and uses finitely many commensurator letters.
  free-generalized-bs-groups-have-type-a-overgroups: that is G = F_k, from Bux--Llosa Isenrich--Wu Remark 12.7; this recovers it, since F_k is a non-cocompact arithmetic lattice in PSL_2(R), and adds surface groups, arithmetic hyperbolic manifold groups and higher-rank lattices.
  bs-class-with-faithful-member-lies-in-type-a-class: that turns one faithful member into BS_G ⊆ B_A; this supplies the faithful member.
---

**ESTABLISHED** through `arithmetic-lie-lattices-faithful-bs-proof` (lane proof;
not independently reviewed; no priority claimed).

**Setting.** `L` is a connected semisimple real Lie group with trivial center and
no compact factors. `G <= L` is an irreducible lattice. `Comm_L(G)` is its
commensurator in `L`.

**Lemma (faithful Hecke member).** Let `c_1, ..., c_r ∈ Comm_L(G)` be such that
`D = ⟨G, c_1, ..., c_r⟩` is not discrete in `L`. Put `G_i = G ∩ c_i^{-1} G c_i` and

    H = ⟨ G, t_1, ..., t_r | t_i x t_i^{-1} = c_i x c_i^{-1}  (x ∈ G_i, 1 <= i <= r) ⟩.

Then `H ∈ BS_G`, and `H` acts faithfully on its Bass--Serre tree.

**Theorem.** If `Comm_L(G)` is not discrete, some such `H` exists. Hence
`BS_(G') ⊆ B_A` for every group `G'` abstractly commensurable with `G`.
`Comm_L(G)` is dense, in particular not discrete, whenever `G` is arithmetic
(Borel). By Margulis's commensurator criterion it is non-discrete exactly when `G`
is arithmetic.

**Instances**, each with `BS_G ⊆ B_A`:
1. **Closed surface groups** of genus `>= 2`. They are all abstractly
   commensurable (`S_g` covers `S_2` with degree `g-1`), and some torsion-free
   cocompact arithmetic Fuchsian group, for example from a quaternion algebra over
   `Q`, is one of them. So every finite graph of groups whose vertex and edge
   groups are commensurable with a surface group, with finite-index edge
   inclusions, embeds in a finitely presented simple group. Examples are the HNN
   extensions of a surface group identifying two finite-index subgroups.
2. **Free groups** `F_k`, `k >= 2`: finite-index torsion-free subgroups of
   `PSL_2(Z)`. This recovers BLIW Theorem 12.5 and Remark 12.7.
3. **Arithmetic hyperbolic manifold groups** in `PO(n,1)^0`, `n >= 2`, and
   arithmetic complex-hyperbolic lattices.
4. **Irreducible lattices in higher rank** (real rank `>= 2`). By Margulis's
   arithmeticity theorem, cited and not re-read, all of them are arithmetic.

**Not covered.** Non-arithmetic lattices, for example Gromov--Piatetski-Shapiro
lattices in `PO(n,1)`. Their commensurator is a finite extension of `G`, so every
group `D` above is discrete, and the lemma gives nothing.
