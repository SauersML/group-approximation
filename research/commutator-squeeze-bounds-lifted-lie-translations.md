---
rg: 2
id: commutator-squeeze-bounds-lifted-lie-translations
kind: claim
title: If a polynomially repetitive Z^d-subshift has a factor carrying a free action of a compact Lie group whose translations lift to automorphisms, and the coding's singular set has positive codimension along the orbits, then the lifted translations form a virtually abelian group; so target T1 is impossible for linearly repetitive rows with tame singular sets
requires:
  - hierarchical-tilings-fail-the-free-commutant-test
  - ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
distinct_from:
  polygonal-anzai-codings-lift-only-finitely-many-rotations: that uses slope bookkeeping for one abelian polygonal example; this uses measure and group structure (commutators contract displacement quadratically while cellular-automaton radius at most doubles), for every compact Lie group and every singular set of positive codimension, with no smoothness.
  hierarchical-tilings-fail-the-free-commutant-test: that shows hierarchical skeletons alone fail the F_2 test and reduces lifting to expansive slabs; this bounds what any continuous Lie data layer can lift, given polynomial repetitivity.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary; not reviewed; no priority
claimed). The recalled inputs are:
- the commutator estimate in compact Lie groups;
- the Tits alternative;
- the structure of compact solvable connected Lie groups (tori).

The result **rules out target T1 in the linearly repetitive, tame regime.** It names exactly the
hypotheses a construction must break.

## Setting

- `Y ⊆ A^(Z^d)` is a subshift with an invariant Borel probability measure `μ`.
- `ψ(R)` is the minimum of `μ([p])` over the nonempty patterns `p` on `B_R`.
  - `Y` is **polynomially repetitive** if `ψ(R) ≥ c R^(-a)`.
  - Linear repetitivity (every `R`-pattern occurs in every ball of radius `CR`) gives this with `a = d`,
    for the unique invariant measure. Self-similar and fixed-point tilings with constant zoom are of this
    kind.
- `ρ : Y → Z` is a factor map. `K` is a compact Lie group with a bi-invariant Riemannian metric and
  `B_K(ε)` its `ε`-ball. `K` acts continuously on `Z` on the right, commuting with `Z^d`.
- `G ≤ Aut(Y)`, and `κ : G → K` is a homomorphism with `ρ ∘ g = R_(κ(g)) ∘ ρ` for all `g ∈ G`. Freeness
  of the `K`-action is not needed.
- The **singular set** is `Z_1 = ⋃_(a≠b) ρ([a]) ∩ ρ([b])`, and `ν = ρ_*μ`.
- **(Cod_s)**: `ν(Z_1 · B_K(ε)) ≤ C ε^s` for small `ε`, with `s > 0`. Tame singular sets satisfy it, for
  example piecewise-smooth hypersurfaces meeting the orbits transversally, with `s = 1`.
- `R(g)` is the larger of the radii of the local rules of `g` and `g^(-1)`.

## Statement

1. **Displacement–radius inequality.** For every `g ∈ G` with `κ(g) ∈ K°` and `κ(g)` acting
   nontrivially on `Z`:

   `ψ(R(g)) ≤ ν( Z_1 · B_K(d(κ(g), 1)) )`.

2. **Commutator squeeze.** Assume polynomial repetitivity and (Cod_s). Then `κ(G)` is **virtually
   abelian** whenever `K` acts freely on `Z`. In particular `κ(G)` contains no `F_2`.
3. **Consequences.**
   - (a) **T1 needs one of three escapes.** In the setting of T1, suppose the row is polynomially
     repetitive and its singular set satisfies (Cod_s). Then the fibre-preserving automorphisms are
     virtually abelian, so every finitely generated subgroup of the automorphism group is virtually solvable, and the group is amenable. This is
     consistent with (RA_free). A construction of T1 must therefore have one of:
     - pattern frequencies decaying faster than every power of `R` (not polynomially repetitive; for
       example variable zoom growing fast);
     - a singular set of fibre codimension `0`, meaning `ν(Z_1 · B_K(ε))` decays slower than every power
       of `ε`;
     - a non-Lie `K`, which is the T2 regime.
   - (b) **Polynomial growth is essential.** Over groups of exponential growth, `ψ(R)` may decay
     exponentially in `R`, so `ψ(2^j)` decays doubly exponentially and the squeeze fails. This fits the
     rigid boundary rows over free groups.
   - (c) **T2 is not touched.** In `∏_i SU(n_i)` there is no uniform commutator estimate for the weighted
     product metric, so non-Lie layers escape. That matches the infinite-dimensionality forced by
     non-exactness in `profinite-skew-layers-collapse-into-the-equicontinuous-factor`.

## Proof

**1.**
- *A cylinder of changed symbols.* `g ≠ id`, since `κ(g)` acts nontrivially and `ρ` is onto. So there is
  `y` with `(gy)(0) ≠ y(0)`. Let `W = [y|_(B_R)]` with `R = R(g)`. Every `y' ∈ W` has
  `(gy')(0) = (gy)(0) ≠ y(0) = y'(0)`, since the local rule reads `B_R`.
- *Each such point projects near `Z_1`.* Let `y' ∈ W`, `z = ρ(y')`, `k = κ(g)`, `a = y'(0)` and
  `b = (gy')(0)`. Then `z ∈ Q_a := ρ([a])` and `zk = ρ(gy') ∈ Q_b`.
  - Take a geodesic `γ` from `1` to `k` in `K°`, of length `d(k, 1)`, and follow the path `t ↦ zγ(t)`.
  - If `zk ∈ Q_a`, then `zk ∈ Q_a ∩ Q_b ⊆ Z_1`.
  - Otherwise let `t*` be the first time the path leaves `Q_a`. Then `zγ(t*) ∈ Q_a`, and it is a limit of
    points of `⋃_(b'≠a) Q_(b')`. The cells are finitely many and closed, so `zγ(t*) ∈ Q_a ∩ Q_(b') ⊆ Z_1`.
  - In both cases `z ∈ Z_1 · B_K(d(k, 1))`.
- *Measure.* `ψ(R) ≤ μ(W) ≤ μ(ρ^(-1)(Z_1 · B_K(d(k, 1)))) = ν(Z_1 · B_K(d(k, 1)))`.

**2.**
- *Radius and displacement of iterated commutators.* Let `x, y ∈ G` with `κ(x)` and `κ(y)` within `δ` of
  `1`. Put `c_0 = y` and `c_j = [x, c_(j−1)]`.
  - Radii add under composition, so `R(c_j) ≤ 2R(x) + 2R(c_(j−1)) ≤ 2^(j+1)(R(x) + R(y))`.
  - In a compact Lie group, `d([u, v], 1) ≤ C_K d(u, 1) d(v, 1)` for `u, v` near `1`. So
    `d(κ(c_j), 1) ≤ (C_K δ)^j δ`, and all these elements lie in `K°`.
- *The squeeze.* If every `κ(c_j) ≠ 1`, then item 1 with polynomial repetitivity and (Cod_s) gives
  `c 2^(-a(j+1)) (R(x) + R(y))^(-a) ≤ C δ^s (C_K δ)^(sj)` for all `j`.
  - If `δ < δ_* := 2^(-a/s)/C_K`, the right side decays exponentially faster than the left. That is a
    contradiction for large `j`.
  - So **`κ(G)` has no pair `κ(x), κ(y)` in `B_K(δ_*)` generating a free group**: in a free group,
    iterated commutators of a free pair are never trivial.
- *No free subgroup.* Suppose `κ(G) ⊇ F ≅ F_2`, and let `L` be the closure of `F`.
  - If `L°` were abelian, then `F ∩ L°`, of finite index in `F`, would be abelian. That is impossible.
  - So `L°` is non-abelian, and `F ∩ B_K(δ)` (which lies in `L°` for small `δ`) is not commutative.
  - Two non-commuting elements of a free group generate a free group of rank 2, which contradicts the
    previous bullet.
- *Virtually abelian.* `κ(G)` is a linear group without `F_2`, hence virtually solvable (Tits).
  - The closure of a virtually solvable subgroup of a compact Lie group has a solvable compact connected
    identity component, which is a torus.
  - So `κ(G) ∩ L°` is abelian and of finite index.
- *Nontrivial action.* `κ(c_j) ≠ 1` gives nontrivial action because `K` acts freely.

**3(a).** By item 3 of the collapse node, the fibre-preserving automorphisms embed in `K` through `κ`.
For a finitely generated `G ≤ Aut(Y)`, the quotient `G/(G ∩ Aut_0)` is abelian and `G ∩ Aut_0` is virtually
abelian by item 2. So `G` is virtually solvable, and `Aut(Y)` is amenable. The rest is item 2. ∎

## Minimality of skeleton-plus-data designs (the coordinator's check)

- A data layer that stores the orbit point of every macrotile keeps the SFT minimal only if
  neighbouring macrotiles are forced to carry consistent orbit points at every level, **including across
  infinite seams**. Otherwise seam configurations carrying two different points of `Z` form a closed
  invariant set that misses the generic orbit.
- The E1 construction (74597e3ce, gluing `Z` for minimality) is the recorded way to achieve this.
- Item 2 shows that minimality is not the binding constraint for T1. Polynomial repetitivity together
  with a tame singular set already excludes it, minimal or not.

## Lesson for general BH

**Commutators squeeze Lie commutants.**
- In a row whose patterns recur polynomially often, every automorphism lifting a translation `k` of a
  Lie layer pays a radius that grows as a power of `1/d(k, 1)`.
- Iterated commutators of two small translations shrink geometrically in displacement, but their radius
  only doubles per step. So only virtually abelian groups of Lie translations can lift.

The free commutant that a time-lift refutation of (RA_free) needs must come from rare patterns
(non-repetitive rows), thick singular sets, or an infinite-dimensional layer. The polynomial growth of
`Z^d` is exactly what makes the squeeze work. It is also exactly what (RA_free) is about: amenable rows
with invariant measures.
