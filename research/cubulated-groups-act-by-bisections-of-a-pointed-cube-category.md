---
rg: 2
id: cubulated-groups-act-by-bisections-of-a-pointed-cube-category
kind: claim
title: A group acting freely and cocompactly on a CAT(0) cube complex acts on the regular part of its Roller boundary by bisections of the left regular groupoid of a finite-object category of pointed cubes, whose normal forms are the Niblo--Reeves normal cube paths
distinct_from:
  prefix-replacement-actions-recode-into-germ-extensions-of-v: that codes by a rank-one path space, which fails on products of trees (Attempt 3 of virtually-torsion-free-cubulated-groups-satisfy-boone-higman); this codes geodesics modulo square flips, so different hyperplane directions shift independently.
  cocompact-tree-product-lattices-lie-in-type-a-class: that is the product-of-trees case, where the category is the cube k-graph; this is the same construction for an arbitrary CAT(0) cube complex, with a trace-type category in place of a k-graph.
  automatic-groups-embed-in-corner-germ-extensions: that uses a rank-one normal-form path space and singular corner points; this avoids singular points on the regular boundary by using a higher-rank category.
---

**ESTABLISHED** through `cubulated-pointed-cube-category-proof` (lane proof,
elementary apart from standard CAT(0) cube complex facts; not independently reviewed;
no priority claimed).

**Setting.** `X` is a locally finite, finite-dimensional CAT(0) cube complex and `G`
acts on `X` by cubical automorphisms, freely on vertices and cocompactly (for
instance `G` torsion-free cubulated). For vertices `y, z`, `H(y, z)` is the set of
hyperplanes separating them; the same notation is used when one point is in the
Roller boundary `∂_R X`.

**1. States are cubes.** For a vertex `y` and a point `x ≠ y` of `X ∪ ∂_R X`, the set
`Max(x, y)` of hyperplanes in `H(x, y)` adjacent to `y` is the hyperplane set of a
cube at `y`.

**2. Geodesic concatenation is local.** For vertices `x, y, z`, the path
`x → y → z` is geodesic (`H(x,y) ∩ H(y,z) = ∅`) if and only if
`Max(x, y) ∩ Max(z, y) = ∅`. Then `Max(x, z) = Max(y, z) ∪ {H ∈ Max(x, y) : H adjacent
to z}`.

**3. The category.** `C_X` has objects the `G`-orbits of pointed cubes `(y, κ)`
(`κ` a cube at `y`, possibly `{y}`), and morphisms the `G`-orbits of triples
`(y, κ, z)` such that `x_κ → y → z` is geodesic, where `x_κ` is the corner of `κ`
opposite `y`. The range is `[(y, κ)]`, the source is `[(z, κ(x_κ, z))]` with
`κ(x_κ, z)` the cube of `Max(x_κ, z)`, and composition is concatenation. It is a
left and right cancellative small category with finitely many objects. Every morphism
factors canonically into morphisms of the finite set `S` of triples `(y, κ, z)` with
`z` the far corner of a nontrivial cube at `y`: the factorization is the Niblo--Reeves
normal cube path from `y` to `z`. (That `S` is a Garside family in Li's sense is
expected but is listed among the gates below.)

**4. The action.** Infinite paths from the base object `[(o, {o})]` (increasing
sequences of morphisms, up to refactorization) are in bijection with `∂_R X`, through
`ω ↦ [o, ω)` modulo square flips. Let `R ⊆ ∂_R X` be the
`G`-invariant set of points `ω` such that the ray `[o, ω)` eventually leaves the
carrier of every hyperplane. Every `g ∈ G` is, near each point of `R`, given by one
compact open bisection `λw ↦ μw` of the left regular groupoid of `C_X`.

**Consequence.** If `R` is closed and `G` acts faithfully on it, then `G` embeds in
the topological full group `F((I_l ⋉ R)_Y^Y)` of `C_X`, with `Y` the cylinder of the
base object. By X. Li (arXiv:2110.04505v2, Theorem `intro:Gars`) that group is of type
`F_∞` once `C_X` satisfies Li's conditions (St), (LCM) and (`t < d`). With the
power-and-phase and `O_2`-stabilization steps of
`tree-lattice-kgraph-power-phase-proof` and
`stabilized-kgraph-full-groups-have-type-a-actions`, that would put `G` in `B_A`.

**Calibrations.**
- `X` a product of thick trees: `R = ∏ ∂T_j`, closed, and `C_X` restricted to
  `R` is the cube `k`-graph of `cocompact-tree-product-lattices-lie-in-type-a-class`.
- `X` the Salvetti cover of a RAAG `A_Γ`: morphisms are reduced traces over the
  signed alphabet `V^±`, the state is the set `Max(t)` of final letters, and `t s` is
  reduced iff `Max(t)^{-1} ∩ Min(s) = ∅`.

**Open gates for BBCMP Question 1.15.** Closedness of `R` (or passage to its closure),
faithfulness on `R` (BBCMP pass to `G * Z` for faithfulness on the whole Roller
boundary), and Li's conditions (St), (LCM), (`t < d`) for `C_X`, after a power and a
phase, together with the identification of `R` with a closed invariant subspace of
Li's `Ω_∞` and the Garside property of `S`. None is checked here, even for RAAGs.

## Lesson for general BH

A rank-one host (a germ extension of `V`) fails for groups with flats because one
element shifts different hyperplane directions by different amounts. Coding by
geodesics modulo square flips fixes this: concatenation is then decided by a finite
local state (a cube), so the Roller-boundary action becomes a finite-state action
by bisections of a higher-rank category. The general mechanism is "finite local
state for composability ⇒ finite-object category ⇒ Li finiteness conditions". It
turns Boone--Higman for any group with such a geodesic structure into a finite
combinatorial check on one category.

## Attempt 1 (bh-free-36, 09-18): which of Li's gates survive with a degree map

Read at source in arXiv:2110.04505v2: Theorem `thm:deg` (TeX l.2055--2063), the
degree-map setting with (UFP*) (l.1835--1840), condition (`t < d`) (l.1611), and its
sufficient Lemma `lem:deg--t<d` (l.2093).
- **Theorem `thm:deg` needs only (F) and (`t < d`).** Its hypotheses are: `P` right
  Noetherian with conditional lcms, a finite Garside family `S_P` with `(S_P^{≤L})^♯`
  closed under left divisors, and a degree map `d: C → P` with (UFP*). Conditions
  (St) and (LCM) of `intro:Gars` are derived by Li inside this setting.
- **Special cube complexes, including the RAAG calibration.** Type the hyperplanes
  through a local isometry to a Salvetti complex. Then `d: C_X → A_Γ^+` (forget signs
  and states) has (UFP*), because prefixes of a reduced signed trace are the lifts of
  prefixes of its unsigned image. `A_Γ^+` is right Noetherian with conditional lcms.
  The nonempty cliques form a finite Garside family (Cartier--Foata normal form), and
  products of at most `L` cliques are the traces of height at most `L`, closed under
  left divisors. `C_X` is cancellative, so (F) holds. **So the RAAG calibration
  reduces to (`t < d`) alone**, together with the choice of the closed invariant
  subspace (`∂Ω`, or the closure of `R`).
- **Why (`t < d`) is not automatic here.** Li's sufficient lemma uses left
  reversibility of `P` (any two elements have a common right multiple). That makes
  `∂Ω(v; e) = ∅` for `e ≠ ∅`, so only the expansions `γ(s)` of full cylinders need a
  repeated piece. `A_Γ^+` is not left reversible unless `Γ` is complete. So the
  expansions `γ(e, s)` with `e ≠ ∅` (cylinders minus the cylinders of some cliques)
  must be shown to contain two pieces equal to `X(v; e)`, possibly after replacing
  `S` by a power.
- **Non-special complexes.** A degree map with (UFP*) to a trace monoid exists exactly
  when some `G`-invariant colouring of hyperplanes makes every heap `H(y, z)` a trace
  heap: same colour never crosses, and adjacent colours are reordered only when the
  hyperplanes cross. This holds for products of trees (to `N^k`) and for special
  complexes, and fails when a hyperplane orbit crosses itself. Otherwise conditions
  (St) (l.1219) and (LCM) (l.1328) of `intro:Gars` must be checked directly.

**Lesson for general BH.** Over a well-behaved degree monoid, finite presentation
of the boundary full group comes down to one multiplicity condition, (`t < d`):
every basic clopen piece must reappear at least twice in its own expansion. This is
the precise combinatorial form of "self-similar with branching at least 2" that a
general Boone--Higman host needs.
