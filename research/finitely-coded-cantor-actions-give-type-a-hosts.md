---
rg: 2
id: finitely-coded-cantor-actions-give-type-a-hosts
kind: claim
title: Any group acting faithfully in the full group of a finitely coded, piecewise strongly connected Cantor groupoid lies in the type (A) class, provided the Cuntz-stabilized full group is finitely presented
distinct_from:
  degree-category-full-groups-stabilized-have-type-a-actions: that assumes finite unit groups; this allows arbitrary unit groups, such as self-similar groups, and isolates comparison as the only structural input, with finite presentation the only analytic one.
  fp-full-binary-cantor-groups-have-type-a-actions: that needs a standard binary V inside the host; this replaces V by the Cuntz factor together with a combinatorial comparison lemma.
  finite-k-graph-full-groups-have-exponential-word-problem: that bounds what finite-unit hosts can contain; this names the host class and says how its reach grows with the unit groups.
---

**ESTABLISHED** through `finitely-coded-cantor-actions-type-a-proof` (lane proof;
not independently reviewed; no priority claimed).

**Definitions.**
- **Finitely coded.** An ample groupoid `𝒢` on a compact space is finitely coded if
  it is Li's boundary groupoid `I_l(ℭ) ⋉ ∂Ω` of a left cancellative small category
  `ℭ`, reduced to a union `Z` of object boundaries, where:
  - `ℭ` has finitely many objects;
  - `ℭ` has a degree map `d : ℭ -> N^k` whose invertibles are the morphisms of
    degree 0, and it satisfies (UFP*): factorization of degrees is unique up to a
    unit in between;
  - finitely many morphisms of each degree end at each object, counted modulo units;
  - every object is the target of morphisms of every degree.
  The unit groups `ℭ^*(w,w)` are arbitrary.
- **Connected in pieces.** `𝒢` is connected in pieces if the objects split into
  finitely many classes with no morphisms between classes, and within a class any
  object is joined to any other by some morphism.

**Theorem.**
1. **Comparison.** In `𝒢'' = 𝒢 x 𝒢_(O_2)`, any two nonempty clopen subsets of the
   same piece are equivalent by a compact open bisection. This needs nothing about
   loops, units or finiteness.
2. **Host.** If `D = F(𝒢'')` is finitely presented, its action on the nonempty
   proper clopen subsets of `Z x {0,1}^N` is of type (A).
3. **Reach.** So every subgroup of `F(𝒢)` lies in `B_A`, hence embeds in a finitely
   presented simple group. In particular this holds for every group with a faithful
   action on a Cantor set whose elements are global bisections of such a `𝒢`.

**When the finite presentation holds.** By Li, arXiv:2110.04505v2, Theorem `thm:ZS`
and Example `ex:ZS` (III), `D` is of type `F_n` when:
- every object has at least two loops of every colour (obtainable by rescaling
  degrees and a phase skew product, `tree-lattice-kgraph-power-phase-proof`);
- condition (F) holds, for example when `ℭ` is right cancellative or the units act
  faithfully on cylinders;
- every unit group is of type `F_n`.

**Instances on main.**
- **Brin–Thompson and Katsura–Exel–Pardo.** Brin–Thompson `nV`, and the odometer host
  `odometer-2v-is-fp-simple-and-contains-bs12`.
- **Self-similar groups.** Finitely presented self-similar groups (one object, with the
  group as units), recovering `fp-self-similar-subgroups-satisfy-permutational-boone-higman`.
- **Tree-product lattices.** All faithful cocompact lattices on products of thick
  trees (`cocompact-tree-product-lattices-lie-in-type-a-class`).
- **Ã₂ lattices.** All cocompact Ã₂ lattices (`a2-lattices-satisfy-permutational-boone-higman`).

**Limits.**
- **Complexity.** With finite unit groups, every subgroup of `F(𝒢)` has word problem
  solvable in exponential time (`finite-k-graph-full-groups-have-exponential-word-problem`,
  stated for k-graphs; the same count applies with finite units). So universal
  reach needs the unit groups to carry the complexity.
- **Central extensions.** Extending a coded action of `C̄` to a central extension `C`
  goes through a free `A`-cover of the Cantor `C̄`-space, which is always a skew
  product (`central-extension-untwisting-over-boundaries`). So this is impossible
  when the extension class survives on point stabilizers. `C` could still have an
  unrelated coded action.

**Lesson for general BH.**
- **Where the difficulty sits.** Comparison and type (A) are free: the Cuntz factor
  makes every finitely coded, piecewise strongly connected Cantor groupoid a type (A)
  host once its full group is finitely presented. So for any group, Boone–Higman in
  its strong, permutational form reduces to two concrete inputs:
  - a faithful Cantor action coded by a finite degree category;
  - Li-type finite presentation of the stabilized full group.
- **What remains.** A universal route must supply these codings with complicated unit
  groups; finite unit groups give exponential word problems. It must also avoid
  central-extension obstructions at stabilizers.
