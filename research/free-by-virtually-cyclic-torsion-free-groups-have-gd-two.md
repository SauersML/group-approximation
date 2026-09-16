---
rg: 2
id: free-by-virtually-cyclic-torsion-free-groups-have-gd-two
kind: claim
title: Torsion-free free-by-(tree-acting) groups have geometric dimension at most two
distinct_from:
  eilenberg-ganea-conjecture: that is the conjecture for every group of cd 2; this is a proved special case, for groups with a free normal subgroup whose quotient acts on a tree with finite stabilizers.
  bb-kernel-gd-two-if-l-lies-in-contractible-2-complex: that builds 2-complexes for Bestvina-Brady kernels by Morse theory; this builds a graph of free groups from a tree action of a quotient.
artifacts:
  - research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md
---

Let `G` be a torsion-free group and `N ⊲ G` a free normal subgroup of any rank. Suppose
`Γ = G/N` acts on a simplicial tree `T` without inversions and with finite vertex
stabilizers. Then `G` has a `K(G,1)` of dimension at most 2. In particular
`gd G = cd G ≤ 2`, so the Eilenberg--Ganea conjecture holds for `G`.

The hypothesis on `Γ` holds in two cases:
- `Γ` is virtually infinite cyclic, via an explicit action on the line built by
  transfer (see the proof route); or
- `Γ` is finite, acting on a point. Then `G` is free.

It also holds if `Γ` is finitely generated and virtually free (Karrass--Pietrowski--Solitar,
recalled, unverified pin).

The class contains:
- every free-by-cyclic group `F ⋊ Z`, with `F` of any rank;
- every torsion-free group in which such a subgroup has finite index and its fibre `F` is
  normal;
- every torsion-free (free)-by-(finitely generated virtually free) group, such as
  torsion-free finite extensions of `F_n × Z`.

Novelty: I did not find this stated in the sources this lane checked (arXiv listings for
"Eilenberg-Ganea" and "virtually free-by-cyclic", checked 2026-09-16). The proof combines
standard tools (Serre, Stallings--Swan, Bass--Serre, Scott--Wall), so it may well be
folklore. Its role here is a reusable lemma for
`torsion-free-virtually-free-by-cyclic-groups-have-gd-two`.
