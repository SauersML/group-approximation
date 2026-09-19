---
rg: 2
id: hyperbolic-lattice-rigid-measures-are-hyperplane-tight
kind: claim
title: Over a finitely generated non-elementary discrete group of isometries of H^n, every invariant probability measure on a quantum-rigid subshift lives on points determined by their restriction to a thick slab around a totally geodesic hyperplane; free, minimal, measured counterexamples to amenability over surface groups must be such hyperplane-tight spacetimes
distinct_from:
  rigid-subshifts-over-free-factors-are-tight-almost-everywhere: that proves slab tightness of invariant measures over Λ_0 × F_n, from the ends of the free factor; this proves hyperplane tightness over one-ended hyperbolic lattices, which have no ends and no free factor, by orienting infinite cuts.
  quantum-rigid-subshifts-are-determined-by-thick-collars: that proves one free side per thick cut; this applies it to the Λ-invariant family of hyperplane cuts and turns the orientations into a boundary point or a finite centre, neither of which an invariant measure allows.
  rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient: that bounds the hole density of a rigid Toeplitz shift by the cost; this adds, over surface groups, that regular ones are never rigid and measured ones must be hyperplane-tight almost everywhere.
  wall-orientation-subshifts-are-quantum-rigid: that poses rigidity of wall-orientation subshifts as the test of (RA′); this shows that in the measured setting the same orientation argument closes over H^n, and it names what fails for walls of a non-exact group.
---

**ESTABLISHED** for items 1–4 (lane proof, elementary given recalled hyperbolic geometry; bh-ra-proof,
2026-09-19; **Referee PASS** bh-ref-q11 2026-09-19, with one precision on item 4(b); no priority claimed). It addresses (RA_free) and (RA_fin), the measured forms,
over hyperbolic lattices. (RA′) at Osajda's group is not touched.

## Setting

- `Λ ≤ Isom(ℍ^n)`, `n ≥ 2`, is finitely generated, discrete and non-elementary, with a word metric
  `d_Λ`. Fix `o ∈ ℍ^n` and `K = max_s d(o, s o)`, so that `d(λo, λ'o) ≤ K d_Λ(λ, λ')`.
- `X ⊆ A^Λ` is a subshift (finite type not assumed), `D`-quantum rigid over some field. Put `W = 2DK`.
- `𝒢` is a countable, `Λ`-invariant family of totally geodesic hyperplanes that is dense in the space of
  hyperplanes; the `Λ`-orbit of a countable dense family will do.
- For `γ ∈ 𝒢` there are two closed half-spaces `H^±(γ)`, and:
  - the *slab* `M_γ = {λ : d(λo, γ) ≤ W}`;
  - the *sides* `P^±_γ = {λ : λo ∈ H^±(γ), d(λo, γ) > W}`.
- `x` is *tight at `γ`* if every `y ∈ X` with `y = x` on `M_γ` equals `x`. Let `T` be the set of points
  tight at some `γ ∈ 𝒢`.

## Theorem

1. **Hyperplane cuts.** `Λ = P^+_γ ⊔ M_γ ⊔ P^-_γ` with `d_Λ(P^+_γ, P^-_γ) > 2D`. So if `x` is not tight
   at `γ`, exactly one closed half-space `H_γ(x)` contains the orbit points of all the variation of
   `x|M_γ`. Moreover `H_(gγ)(gx) = g H_γ(x)`.
2. **Consistency.** If `x` is tight at neither `γ` nor `γ'`, then `d(H_γ(x), H_(γ')(x)) ≤ 2DK`.
3. **Measures are hyperplane-tight.** Every `Λ`-invariant Borel probability measure `μ` on `X` satisfies
   `μ(T) = 1`. If `Λ` is a lattice, `μ`-almost every point is tight at infinitely many hyperplanes of
   `𝒢`.
4. **Consequences.**
   - (a) **(RA_fin) and (RA_free) over hyperbolic lattices.** Suppose an infinite, minimal, rigid subshift
     over a surface group (or any lattice in `Isom(ℍ^n)`) carries an invariant measure. Almost every
     point is then determined by its restriction to one thick hyperplane slab. An invariant measure
     exists, for example, when the subshift is finite-to-one over its equicontinuous factor, or is a
     regular Toeplitz shift. The shape is the same as the tight spacetimes of `Λ_0 × F_n`.
   - (b) **Toeplitz over surface groups.** A surface group of genus `g ≥ 2` has fixed price `2g − 1`,
     and `β₁⁽²⁾ = 2g − 2` (Gaboriau, recalled). So every Farber chain has rank gradient `2g − 2`
     (Abért–Nikolov).
     - A rigid Toeplitz shift over it has holes of density `≥ 2(2g−2)/|B_(2D)|` at every level with
       `inj > 4D`, along its own period chain
       (`rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient`).
     - **So no regular Toeplitz shift over a surface group is quantum rigid.** The same holds over every
       group of fixed price `> 1`.
     - An irregular rigid one, if it carries an invariant measure, is line-tight almost everywhere by
       item 3.
   - (c) **Group subshifts.** An infinite quantum-rigid group subshift over a lattice `Λ` has an injective
     restriction map to some hyperplane slab `M_γ`. It is a uniformly tight spacetime along a
     hyperplane.

## Proof

1. **Cuts.**
   - Let `λ ∈ P^+`, `λ' ∈ P^-` with `d_Λ(λ,λ') ≤ 2D`. Then `d(λo, λ'o) ≤ 2DK`, and the geodesic segment
     between them crosses `γ` at some `q`. So one endpoint is within `DK < W` of `γ`, which is a
     contradiction.
   - Now apply item 1 of `quantum-rigid-subshifts-are-determined-by-thick-collars` to `ω = x|M_γ`. All
     extensions agree with `x` on `P^+`, or all agree on `P^-`. If `x` is not tight, some extension
     differs from `x`, so exactly one side varies.
   - Equivariance holds because `g` maps slabs and sides to slabs and sides, and `𝒢` is invariant.
2. Take `y ≠ x` agreeing with `x` on `M_γ`, and `y' ≠ x` agreeing with `x` on `M_(γ')`. Their difference
   sets have orbit points in `H_γ(x)` and in `H_(γ')(x)`.
   - If those half-spaces are more than `2DK` apart, the difference sets are more than `2D` apart in
     `Λ`.
   - Lemma 1 of `quantum-rigid-subshifts-cluster-the-modifications-of-each-point` then refutes
     rigidity.
3. `X ∖ T` is invariant. If it had positive measure, normalize `μ` on it. So assume that almost every
   `x` is tight at no `γ ∈ 𝒢`; then `H_γ(x)` is defined for every `γ`.
   - Write `t(γ) = d(o, γ)`, and call the side of `γ` not containing `o` its *far side*. Let `X_I` be the
     set of `x` with far chosen sides at arbitrarily large depth, and `X_II` the rest. Both are
     invariant, because moving the basepoint shifts depths by a bounded amount.
   - **Case I (a boundary point).**
     - The ideal boundary of a far side at depth `t` is a closed cap of visual diameter `≤ C e^(−t)`
       (recalled).
     - Take two far chosen sides at depths `> R`.
       - If the hyperplanes are more than `2DK` apart, item 2 excludes facing away. For far sides of
         disjoint hyperplanes the only other option is nesting, so the caps intersect. If the
         hyperplanes cross, the quadrant `H ∩ H'` is unbounded, and again the caps intersect.
       - If they are within `2DK`, both caps contain the visual projections of points at mutual distance
         `≤ 2DK` and at depth `> R`. So the caps are within `C e^(2DK − R)` of each other.
     - Hence the union `S_R` of far chosen caps at depth `> R` has visual diameter `≤ C′ e^(−R)`. It is
       nonempty in Case I and decreases in `R`, so `⋂_R cl S_R = {ξ(x)}`.
     - `ξ` is measurable and equivariant: a change of basepoint changes `S_R` only up to a shift of `R`.
       So `ξ_*μ` would be a `Λ`-invariant probability measure on `∂ℍ^n`. A non-elementary group has none
       (recalled). So `μ(X_I) = 0`.
   - **Case II (a finite centre).**
     - Call `p` *`ρ`-central* for `x` if every `γ ∈ 𝒢` with `d(p, γ) > ρ` has `p ∈ H_γ(x)`. In Case II,
       `o` is `R(x)`-central.
     - If `p` is `ρ`-central, then `p'` is `(ρ + d(p,p'))`-central, since a hyperplane farther than
       `d(p,p')` from `p'` does not cross `[p,p']`. So `ρ_x(λ) = inf{ρ : λo is ρ-central}` is finite.
     - `ρ_x(λ) → ∞` as `λ → ∞`. Otherwise there are `λ_k o → ∞` that are all `ρ_0`-central. By density
       some `γ_k ∈ 𝒢` separates `o` from `λ_k o` at distance `> max(R(x), ρ_0)` from both, near the
       perpendicular bisector. Then `H_(γ_k)(x)` contains both points, which lie on opposite sides.
     - Hence `Z(x) = {λ : ρ_x(λ) ≤ inf ρ_x + 1}` is finite and nonempty, measurable, and satisfies
       `Z(gx) = gZ(x)`.
     - Some invariant set `{|Z| = k}` has positive measure; restrict and normalize `μ` there. Push it
       forward to `k`-subsets of `Λ`. By invariance `ν(F ∋ λ)` is constant in `λ`, and its sum over `λ` is
       `k`, so the constant is `0`. That contradicts `F ≠ ∅`. So `μ(X_II) = 0`.
   - **Infinitely many.** Suppose `Tight(x) = {γ ∈ 𝒢 : x tight at γ}` were finite and nonempty on a set
     of positive measure. Then some orbit `Λγ` and some `k ≥ 1` give an invariant set of positive measure
     on which `|Tight(x) ∩ Λγ| = k`. The same counting on `Λγ` gives a contradiction. For a
     lattice these orbits are infinite, since a hyperplane stabilizer has infinite index.
4. (a) is item 3.
   - (b) adds the cost bound of the Toeplitz node. Surface groups have fixed price `2g−1` (recalled).
   - (c) Haar measure is invariant, so some point `x` is tight at some `γ`. For a group subshift,
     `y ∈ E_γ(x)` iff `y − x` vanishes on `M_γ`. So tightness at one point means the kernel of
     restriction to `M_γ` is `0`, and then every point is tight at `γ`. ∎

## Calibration

| Case | Consistent with |
|---|---|
| `F_n` as a Schottky group in `Isom(ℍ^2)` | item 3 is weaker than the known result that invariant measures on rigid subshifts over `F_n` sit on finite orbits (`rigid-subshifts-over-free-factors-are-tight-almost-everywhere`) |
| hyperbolic seed SFTs (b17ce0c51): perfect part factors onto the Gromov boundary | carries no invariant measure |
| the (RA) refuter over `(F_2 × Z) ∗ Z` (`rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`) | not a hyperbolic lattice, and not measured |
| Cornulier-regime coset shifts (measured, rigid, non-amenable) | live over `V`, `F`, `T` and relatives, not over hyperbolic lattices. Item 4(c) predicts that a rigid coset or group shift over a lattice is hyperplane-tight, and none is recorded |

## What this says about (RA′) at Osajda's group

- The argument uses only a family of cuts (here, hyperplane slabs) and two facts about its boundary:
  - chosen sides at depth converge to a boundary point;
  - that boundary carries no invariant probability measure.
- Over a group with walls, the same scheme lands in the wall (Roller) boundary. For a non-exact group,
  such as Arzhantseva–Osajda type walls, that boundary action is not amenable and may carry invariant
  measures. So this obstruction and the candidate counterexample of `wall-orientation-subshifts-are-quantum-rigid`
  sit at the same place. **The measured problem at `G` is: does `G` preserve a probability measure on
  the boundary of its cuts?** (Heuristic; not proved.)

## Lesson for general BH

**Invariant measures on rigid subshifts live on codimension-one tight points.**
- Rigidity orients every thick cut, and the orientations must pairwise meet. So a non-tight point
  chooses either a boundary point or a finite centre.
- An invariant measure allows neither when the cut boundary carries no invariant probability measure.
  That is the case for trees (ends), for `Λ_0 × F_n`, and now for all hyperbolic lattices (spheres).
- So what remains for measured counterexamples is spacetimes determined by one slab. At a non-exact
  group, the remaining question is whether its cut boundary carries an invariant measure.

Credit: Gaboriau (fixed price of surface groups, cost). The visual-metric estimates and the absence of
invariant boundary measures for non-elementary groups are standard (recalled). The cut lemma rests on
bh-star-b's two-piece certificate and clustering (ca15e5298, f676c07d2). The slab-tightness template
is bh-star-b's `Λ_0 × F_n` theorem.

## Referee (bh-ref-q11, 2026-09-19): PASS; one precision on the fixed-price step

**Imports, checked as stated on main.**
- Item 1 of the collars node: for `Λ = P ⊔ M ⊔ N` with `d(P,N) > 2D`, every extension of `ω` agrees with `y` on `P`, or every extension agrees on `N`.
- Lemma 1 of the clustering node: `d(Δ_1, Δ_2) > 2D` refutes rigidity. It holds for **arbitrary**, possibly infinite, difference sets, which is what item 2 needs.

**Items 1–2: correct.**
- The crossing point `q` gives an endpoint within `DK < W` of `γ`.
- If neither side varies, then `x` is tight. So "exactly one side" holds.
- In item 2, difference sets in half-spaces more than `2DK` apart are more than `2D` apart in `d_Λ`.

**Item 3, the measure-concentration step: correct.**
- **Case I (far sides at arbitrarily large depth).** The case analysis for two far chosen sides at depth `> R` is exhaustive:
  - disjoint and far apart: facing away is excluded by item 2, so they are nested (the second hyperplane lies between `o` and the far side), and the caps intersect;
  - crossing: every quadrant is unbounded, so the caps meet;
  - within `2DK`: the visual projections of `2DK`-close points at depth `> R` give caps within `Ce^(2DK−R)`.
- So `diam S_R ≤ 2Ce^(−R) + Ce^(2DK−R)`.
- `ξ` is equivariant: hyperplanes deeper than `d(o, g^{-1}o)` have the same near and far sides for both base points. A non-elementary `Λ` has no invariant probability measure on `∂ℍ^n`.
- **Case II (a finite centre).** Centrality propagates, and the near-bisector hyperplane `γ_k` exists by density. `ρ_x` is proper because the orbit of `o` is locally finite. Then mass transport on `k`-subsets gives `ν(F ∋ λ) = 0`.
- **"Infinitely many".** The same mass transport on an orbit `Λγ` works, because the orbit is infinite for lattices. A finite-index stabilizer of `γ` would put the limit set in `∂γ`. That is exactly where the lattice hypothesis is needed.

**Item 4(a) and 4(c): correct.**
- Finite-to-one extensions of the Haar-measured MEF carry the fibre-uniform measure, since `g` maps fibres bijectively.
- For group subshifts, tightness at one point makes the kernel of restriction to `M_γ` zero.

**Item 4(b): correct, with a precision.**
- **Surface groups.** An index-`k` subgroup has genus `k(g−1)+1`, so `(d(Γ)−1)/k = (2k(g−1)+1)/k ≥ 2g−2` for **every** finite-index `Γ`. The bound needs neither Abért–Nikolov nor fixed price.
- **Fixed price `c > 1`.** A chain has rank gradient `c − 1` only when it is Farber, i.e. the profinite action is essentially free. The wire-net bound also needs `inj(Γ_n) → ∞`.
- Both hold when the Toeplitz period chain has trivial intersection, which is the Toeplitz node's convention.
- If the cores contain a common `N ≠ 1`, then `N` fixes the Toeplitz point and acts trivially on `X`, so the action is not faithful. The claim therefore holds for faithful Toeplitz shifts, and should say so.
- The regularity conclusion is along the period structure, as in that node's referee note.
- This step uses only the Toeplitz node plus cost. It does not use items 1–3.
