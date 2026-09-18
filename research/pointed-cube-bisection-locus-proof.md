---
rg: 2
id: pointed-cube-bisection-locus-proof
kind: route
title: A germ of the pointed-cube groupoid carrying omega to g omega is the prefix replacement of g itself; along a tail inside a hyperplane carrier the last-cube states of z and gz differ forever, and in Z^2 * Z regular c-exits accumulate on the flat point (+infinity, 0)
target: pointed-cube-bisection-locus-is-the-regular-boundary
requires:
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
---

**Lane proof, not independently reviewed.** Notation:
- `H(p,q)` is the set of hyperplanes separating `p` and `q`, and `Max(p,q)` is its subset
  of hyperplanes adjacent to `q`.
- "Adjacent to `H`" means lying in the carrier of `H`.
- **The local rule** (item 2 of the parent). If `x → y → w` is geodesic, then
  `Max(x,w) = Max(y,w) ∪ {J ∈ Max(x,y) : J adjacent to w}`. The rule is `G`-equivariant.

## 1. Identification (item 1)

- `C_X` has lcms (median joins, `pointed-cube-categories-li-garside-proof`), so the
  constructible ideals of the base cone are principal or empty.
- Points of Li's spectrum on that cone are the nonempty directed down-closed sets `D` of
  morphisms `o → z`, i.e. of vertices `z`.
- **From `D` to an ultrafilter.** `D ↦ ω_D` with `H(o, ω_D) = ∪_{z∈D} H(o,z)`.
  - It is consistent: a flipped halfspace and an unflipped one meet at a vertex of `D`,
    and two flipped halfspaces meet at a common upper bound in `D`.
  - It is inverted by `ω ↦ I(o,ω)`: a finite subset of `H(o,ω_D)` lies in some `H(o,z')`
    with `z' ∈ D`, by directedness.
- **Principal points.** The principal points `χ_z` are the vertices. So `Ω_∞ ∩ cone(o)` is
  `∂_R X`.
- **Topology.** Cylinders are the sets `{ω : H(o,z) ⊆ H(o,ω)}`. Conversely, the halfspace of
  `H` away from `o` is the cylinder of the gate projection of `o` onto it. So the two
  topologies agree.

## 2. Regularity

**Lemma (leaving is permanent).**
- **Setup.** Let `p` be adjacent to `H`, and let the edge `pq` be dual to `K` with `q` not
  adjacent to `H`.
- **Then `K ∩ H = ∅`.** First `K ≠ H`. If `K` crossed `H`, the two would span a square at
  `p` containing `pq`.
- **The carrier lies on `p`'s side of `K`.** A carrier cube with a vertex on `q`'s side
  would have an edge dual to `K`, so `K` would cross `H`.
- **Conclusion.** A geodesic that crosses `K` never returns to the carrier of `H`.

**Consequences.**
- `ω` is non-regular iff some hyperplane `H` has all but finitely many vertices of a
  geodesic ray `o → ω` in its carrier.
- This does not depend on the ray. If a ray `γ'` leaves the carrier across `K`, then
  `K ∈ H(o,ω)`. So every other ray `γ` crosses `K` too, and then leaves for good.

## 3. A germ is the element's own prefix replacement

**The germ is a group element.** Suppose `g` agrees near `ω` with `λw ↦ μw`, where
`λ = [o→z]` with `z ∈ I(o,ω)`, `μ = [o→z']`, and `d(λ) = d(μ)`.
- The domains are `[(z, Max(o,z))]` and `[(z', Max(o,z'))]`. Freeness gives a unique `h`
  with `hz = z'` and `h Max(o,z) = Max(o,z')`.
- For `ω'` in the cylinder, `μw` has hyperplane set `H(o,z') ⊔ hH(z,ω')`. On the other
  hand, `H(o,hω') = H(o,hz) Δ hH(z,ω')`, and this symmetric difference is disjoint
  because `μw` is a point. So `μw = hω'`.
- Hence `g = h` near `ω`, and (TF) gives `h = g`.
- So `z' = gz` and `Max(o,gz) = g Max(o,z)`.

**Propagation along a ray.** Let `γ` be a geodesic ray `o → z → ω`, with vertices `z_n`
beyond `z`.
- The `o`-ray of `gω` is `o → gz` followed by `g(γ|_{[z,∞)})`.
- Applying the local rule step by step, equivariantly, gives `Max(o, gz_n) = g Max(o, z_n)`
  for every `n`.

## 4. No germ off `R` (item 2)

**Setup.** Let `ω ∉ R`, with `H` as in §2, `γ` a ray through `z`, and `z_n` in the carrier
of `H` for all `n ≥ n_0`.
- **The element `g`.** Pick `g` with `H ∈ H(g^{-1}o, o)`. It exists because the halfspace
  of `H` away from `o` contains a vertex at distance `> D` from `H`, where `D` bounds the
  distance from any vertex to `Go`. The nearest orbit point `g^{-1}o` is then on that side.
- **Its image.** Then `gH ∈ H(o,go)`, and `gz_n` is adjacent to `gH` for all `n ≥ n_0`.

Suppose `g` had a germ at `ω`. Take `n ≥ n_0` beyond `z`.
- **(a) `ω` does not cross `H`.** Then `H ∉ H(o,z_n)`, so `gH ∉ H(go, gz_n)`, so
  `gH ∈ H(o,gz_n)`. It is adjacent to `gz_n`, so `gH ∈ Max(o,gz_n) = g Max(o,z_n)`.
  That gives `H ∈ H(o,z_n)`, a contradiction.
- **(b) `ω` crosses `H`.** Take `n` beyond the crossing. Then `H ∈ Max(o,z_n)`, so
  `gH ∈ Max(o,gz_n) ⊆ H(o,gz_n)`. But `gH` lies in both `H(o,go)` and `H(go,gz_n)`, so
  `gH ∉ H(o,gz_n)`, a contradiction.

At regular points every `g` has a germ, by item 4 of the parent. This proves item 2, and
item 3 follows at once.

## 5. `Z² * Z` (item 4)

**The complex.** `K` has one vertex, edges `a, b, c` and one square `[a,b]`. Its universal
cover `X` is a tree of flats (copies of the square tiling of `R²`) joined by `c`-edges.
- Hyperplanes dual to `a` or `b` are lines inside a single flat.
- Hyperplanes dual to `c` are single edge midpoints.
- `X` is essential, and `G = Z² * Z` acts freely and cocompactly.

**(TF).**
- Every cylinder `C(z)` contains the points leaving through `z` and then a `c`-edge `ε`.
  These realize every end of the Bass–Serre tree beyond the edge `e` of `ε`.
- An element fixing `C(z)` pointwise fixes all those ends, hence the edge `e`.
- Edge stabilizers of a free product are trivial.

**The non-regular point.** In the base flat `P ∋ o`, the ray `z_k = a^k` gives
`ω = (+∞, 0)`. It stays adjacent to `y = ±1/2` forever, so `ω ∉ R`. Directly, `g = b` has
no germ there: `Max(o, b z_k)` is the square `{x = k−½, y = ½}`, while `b Max(o, z_k)` is
the edge `{x = k−½}`.

**Every invariant `Z` accumulates on `ω`.** Let `Z ≠ ∅` be closed and invariant.
- **`Z` reaches a non-base object.** Removing a nontrivial prefix moves a point of
  `Z ∩ cone(o)` into another cone. The base object `[(o,{o})]` is the domain of no
  non-identity morphism, since `Max(x_κ, z) ≠ ∅` for `z ≠ x_κ`. So `Z` contains a point
  `ξ'` in the cone of some non-base object `v`.
- **Every non-base state is reachable after a `c`-edge.** The ten non-base states are the
  six edges `a^±, b^±, c^±` and the four squares.
  - After a `c`-edge, taking `a^±`, `b^±`, `c^+` or a square gives that state. The old
    `c`-hyperplane is not adjacent to the new vertex.
  - `c^-` is reached by `a^+` then `c^-`, which enters a new flat.
- **The approximating points.** Let `λ_n = o → a^n → a^n c → (path to state v)`. Then
  `λ_n ξ' ∈ Z ∩ cone(o)`.
- **Convergence to `ω`.** Check each hyperplane `J`:
  - the lines `x = k−½` (`k ≥ 1`) are crossed by `ω` and by `λ_n ξ'` for `n ≥ k`;
  - the other hyperplanes of `P` are crossed by neither, since after the `c`-edge the path
    stays in the branch at `a^n` and never returns to `P`;
  - any other `J` lies in the branch hanging off `P` at one vertex, so it is crossed by
    `λ_n ξ'` for at most one `n`.
- So `λ_n ξ' → ω` and `ω ∈ Z`. By item 2, `G` does not act on `Z ∩ cone(o)` by
  bisections. ∎

## Lesson for general BH

The whole obstruction is one line: `Max(o,gz) = g Max(o,z)` must eventually hold along the
tail. It fails exactly while the tail runs beside a wall that `g` moves across the base
point. Checking this line on a coding before building the host would have caught the
failure at once.
