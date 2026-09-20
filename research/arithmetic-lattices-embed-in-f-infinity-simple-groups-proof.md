---
rg: 2
id: arithmetic-lattices-embed-in-f-infinity-simple-groups-proof
kind: route
title: Pass to a torsion-free finite-index subgroup, take its faithful Hecke member, and run Bux–Llosa Isenrich–Wu Theorem 11.1 for every n with one envelope
target: arithmetic-lattices-embed-in-f-infinity-simple-groups
requires:
  - arithmetic-lie-lattices-have-faithful-bs-members
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
  - surface-generalized-bs-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

Let `L`, `Γ` be as in the target. Write `Z = Z(L)`, which is finite, and `π : L → L/Z`.

**Step 1 (a center-free model).** `Γ` is finitely generated and linear through `Ad`, so by Selberg's
lemma it has a torsion-free normal subgroup `Γ_0` of finite index. `Γ_0 ∩ Z` is a finite subgroup of
a torsion-free group, hence trivial, so `π` maps `Γ_0` isomorphically onto `π(Γ_0)`.
- `L/Z` is a connected semisimple Lie group with trivial center and no compact factors.
- `π(Γ_0)` is a lattice in it, irreducible because `Γ` is, and arithmetic because arithmeticity is
  a commensurability property that passes to the adjoint quotient.

**Step 2 (a faithful member).** By `arithmetic-lie-lattices-have-faithful-bs-members` (Theorem, with
`Comm` dense for arithmetic lattices), applied to `π(Γ_0) ≤ L/Z`, the class `BS_{π(Γ_0)}` contains a
nontrivial group `H` acting faithfully on its Bass–Serre tree. `BS` depends only on the abstract
commensurability class, and `Γ ≅_comm Γ_0 ≅ π(Γ_0)`. So `H ∈ BS_Γ`.

**Step 3 (type `F_∞` inputs).** `Γ_0` is of type `F_∞`:
- if `Γ` is cocompact, a torsion-free finite-index subgroup acts freely and cocompactly on the
  contractible symmetric space of `L`, so it is of type `F`;
- if not, `Γ` is arithmetic and non-cocompact, and the Borel–Serre bordification gives a
  torsion-free finite-index subgroup of type `F` (cited).

Type `F_∞` is invariant under passing to finite-index subgroups and finite extensions, so every
vertex and edge group of every graph of groups in `BS_Γ` is of type `F_∞`.

**Step 4 (one envelope for all n).** Bux–Llosa Isenrich–Wu Theorem 11.1, in the `F_n` form of §11
recorded in `research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md`: for `G` of type
`F_n`, `n ≥ 2`, with a nontrivial faithful member of `BS_G`, every `K ∈ BS_G` embeds in a simple group
of type `F_n`. Apply it with `G = Γ_0` and the witness `H` of Step 2, for each `n ≥ 2`.
- The group `L_K ⊇ K` built in the proof glues the graphs of `H` and `K` along a new edge carrying a
  common finite-index subgroup. It does not depend on `n`.
- Neither does the envelope of Theorem 10.5: the twisted Brin–Thompson group of the rigid permutation
  group of the augmented tree, whose viral-expansion triples (Lemma 10.4) are chosen per finite
  vertex set and not per `n`.

This is the reading recorded in step 3 of `surface-generalized-bs-groups-satisfy-boone-higman-proof`,
and it is how Bux–Llosa Isenrich–Wu state their Theorems 12.2–12.5 with type `F_∞`. So one simple
group contains `K` and is of type `F_n` for every `n`, that is, of type `F_∞`.

**Step 5 (instances).** `K = Γ` is the one-vertex graph with no edges, so `Γ ∈ BS_Γ`. The instance
list of the target uses only:
- the cited arithmeticity theorems (Corlette; Gromov–Schoen; Margulis);
- Kostant's property (T) for `Sp(n,1)`, `n ≥ 2`, and `F_4^{(-20)}`, inherited by lattices;
- hyperbolicity of cocompact lattices in rank one, by the Švarc–Milnor lemma on a negatively curved
  symmetric space.
