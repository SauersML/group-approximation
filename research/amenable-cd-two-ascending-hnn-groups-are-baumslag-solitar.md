---
rg: 2
id: amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar
kind: claim
title: An amenable cd-2 ascending HNN extension over a finitely generated base is BS(1,m); a two-dimensional counterexample has empty Σ¹ and only torsion quotients by finitely generated normal subgroups
distinct_from:
  amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical: that excludes EA normal subgroups and commensurated cyclic subgroups, and its item 3 only descends a Σ¹ splitting to the base; this excludes Σ¹ altogether, and excludes every finitely generated normal subgroup with a non-torsion quotient
  amenable-fp-iff-affiliated-top-homology-vanishes: that reduces the dimension-2 case to H_1(G; U(G)) = 0; this proves that vanishing whenever G, or a subgroup, has a Z-quotient with finitely generated kernel or an ascending HNN structure over a finitely generated base
  fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension: that obtains an ascending HNN structure from finite presentability; this assumes the structure and proves finite presentability, in dimension 2 under amenability
  kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop: that proves a cd drop for kernels under FP and Euler-characteristic hypotheses; this gets the drop (to cd at most 1) in amenable dimension 2 with only finite generation of the kernel, and item 5 shows that the drop fails in amenable dimension 3
  bieri-strebel-splitting-over-kernel-of-map-to-z: that splits finitely presented groups; this needs no finite presentability, because the vanishing of H_1(G; U(G)) comes from the structure itself
---

**ESTABLISHED** through `amenable-cd-two-ascending-hnn-bs-proof`, from
`ascending-hnn-quotients-have-vanishing-affiliated-first-homology`,
`amenable-fp-iff-affiliated-top-homology-vanishes` (item 4) and
`amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical` (item 2). Item 5 also cites
Gildenhuys' classification.

Throughout, `G` is an amenable group with `cd_Z G ≤ 2`, so `G` is torsion-free.

1. **Ascending HNN groups.** Suppose `G = ⟨K, t⟩` with `K` finitely generated, `t K t⁻¹ ⊆ K`, and
   some `χ : G → Z` with `χ(K) = 0` and `χ(t) = 1`. Then `G ≅ Z` or `G ≅ BS(1,m)` for some
   `m ≠ 0`. In particular the base `K` is trivial or infinite cyclic.
2. **Finitely generated kernels.** Let `H ≤ G` and `N ⊴ H` with `H/N ≅ Z` and `N` finitely
   generated. Then `N = 1` or `N ≅ Z`, so `cd N ≤ 1`. The same conclusion holds for any finitely
   generated `N ≤ G` and any `g ∈ N_G(N)` with no nontrivial power of `g` in `N`. So if `N ≤ G` is
   finitely generated and not cyclic, then `N_G(N)/N` is a torsion group.
3. **A two-dimensional counterexample.** Let `G` be finitely generated and not solvable, with
   `cd G = 2`. Equivalently, `G` is not virtually solvable and is a counterexample to Kropholler's
   question. Then:
   - (a) `G` is not of the form in item 1, and `Σ¹(G) = ∅`. In particular `G` is not an ascending
     HNN extension over any finitely generated base. This supersedes the descent in item 3 of
     `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`, which can never start.
   - (b) For every nontrivial finitely generated `N ⊴ G`, the quotient `G/N` is a torsion group.
     If also `[G : N] = ∞`, then `G/N` is an infinite, finitely generated, amenable torsion group,
     and `N` is itself a two-dimensional counterexample: finitely generated, amenable, of cd 2,
     and not solvable.
   - (c) No finitely generated normal subgroup of `G` has an infinite elementary amenable
     quotient. This includes the trivial subgroup.
4. **The precise obstruction.** For finitely generated amenable `G` of cd 2 and finitely
   generated `N ⊴ G` of infinite index, `cd N ≤ 1` holds whenever `G/N` is not a torsion group
   (item 2). In a counterexample, `cd N = 1` is impossible for `N ≠ 1`, since then `N ≅ Z` is an
   EA normal subgroup. So the statement "`N` has cd 1" is equivalent, in a counterexample, to
   the non-existence of nontrivial finitely generated normal subgroups of infinite index. The only
   case left is `N ⊴ G` with `G/N` an infinite finitely generated amenable torsion group, in which `N` is again
   a counterexample. The mapping-torus vanishing needs a `Z`-quotient of a subgroup containing
   `N`, and that is exactly what a torsion quotient lacks.
5. **The drop fails in dimension 3.** `Γ = Z[1/6] ⋊ Z²`, with the two generators acting by `×2`
   and `×3`, is amenable (metabelian) of cd 3. It has a finitely generated normal subgroup
   `N = Z[1/6] ⋊_{2/3} Z` with `Γ/N ≅ Z` and `cd N = 3`. So a cd-drop argument for finitely
   generated normal subgroups of infinite index must be specific to dimension 2.
