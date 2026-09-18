---
rg: 2
id: rigid-subshifts-over-free-factors-are-tight-almost-everywhere
kind: claim
title: Over Λ_0 × F_n with n >= 2, an invariant probability measure on a quantum-rigid subshift lives on points determined by one thick slab; over F_n itself every quantum-rigid subshift without isolated points is a continuous extension of the boundary, hence topologically amenable
requires:
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - quantum-rigid-sfts-over-products-have-a-single-free-branch
distinct_from:
  quantum-rigid-sfts-over-products-have-a-single-free-branch: that proves the single-free-branch theorem for SFTs; this proves it for every subshift and shows that the free branches of nested slabs converge to an equivariant end, which no invariant measure can survive.
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the open question (RA); this proves (RA) over F_n, for every rigid subshift without isolated points, and reduces the measure form over Λ_0 × F_n to tight spacetimes.
  free-group-boundary-shifts-are-quantum-rigid: that proves rigidity of the end shift by compression; here the end of a non-tight point is recovered from rigidity alone, and for the end shift it is the coded end itself.
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed; no priority claimed).
It is partial progress on `quantum-rigid-minimal-topfree-subshift-actions-are-amenable`.

## Setting

- `Λ = Λ_0 × F_n`, with `n >= 2` and `Λ_0` finitely generated (possibly trivial).
- The word metric uses `S_0 ∪ S_F`, where `S_F` is a free basis and its inverses, so
  `d((λ,h),(λ',h')) >= d_F(h,h')`, and the Cayley graph of `F_n` is a tree `T`.
- `X ⊆ A^Λ` is a subshift (finite type not assumed), and `D`-quantum rigid over some field.
- Fix `w >= 2D`. For `r >= 0`, the *slab* is `M_r = Λ_0 × B_(r+w)`, where `B_ρ` is the ball in `F_n`.
- For `x ∈ X`, `E_r(x) = {y ∈ X : y = x on M_r}`, and its *variation* is
  `V_r(x) = ⋃_(y ∈ E_r(x)) Δ(x, y)`.
- `x` is *tight at scale `r`* if `E_r(x) = {x}`.

## Lemma 1′ (two-piece certificate)

Let `x, z ∈ A^Λ` be colourings whose `B_D`-patterns all occur in `X`. Suppose `Δ(x, z)` is the union of
two nonempty sets at distance `> 2D`. Then `X` is not `D`-quantum rigid over any field.

*Proof.* The wall family of Lemma 1 in `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`
reads `x` and `z` only through their `B_D`-patterns, in (Q3). ∎

## Theorem

1. **Single free branch, for every subshift.** Let `S ⊆ F_n` be finite, with the components
   `C_1, …, C_m` of `F_n \ S` (`m >= 2`), and deep parts `C_i^w = {h ∈ C_i : d(h, S) > w}`.
   - For every pattern `s` occurring on `Λ_0 × N_w(S)`, there is an `i` such that all extensions of
     `s` in `X` agree off `Λ_0 × C_i^w`.
2. **Nested branches give an end.** Suppose `x` is tight at no scale. Then the branches of item 1 for
   `S = B_r` are nested as `r` grows, and they shrink to an end `ξ(x) ∈ ∂T`.
   - The map `ξ` is defined on the invariant set `X_nt` of such points.
   - It is `Λ_0`-invariant and `F_n`-equivariant.
3. **Invariant measures force tightness.** If `μ` is a `Λ`-invariant Borel probability measure on `X`,
   then `μ(X_nt) = 0`. So `μ`-almost every point is determined by its restriction to one slab
   `Λ_0 × B_R`.
4. **Free groups: (RA) holds.** Let `Λ_0` be trivial, so `Λ = F_n`.
   - (a) Tight points are exactly the isolated points of `X`.
   - (b) If `X` has no isolated points (for example if it is minimal and infinite), then `ξ` is
     defined on all of `X`, is continuous and `F_n`-equivariant, and `F_n ↷ X` is topologically
     amenable. This is (RA) for `F_n`, and it needs no topological freeness.
   - (c) Every invariant probability measure on a quantum-rigid `X` is supported on finite orbits.

## Proof

1. Let `y, y'` extend `s`, and suppose `Δ(y, y')` meets two deep parts, `Λ_0 × C_i^w` and
   `Λ_0 × C_j^w`. Let `z` be `y'` on those two deep parts, and `y` elsewhere.
   - Points of `C_i^w` are at distance `>= w + 2 > 2D` from `F_n \ C_i`.
   - So a `D`-ball meeting `Λ_0 × C_i^w` lies in `Λ_0 × (C_i ∪ N_w(S))`. There `z = y'`, because
     `y = y'` on the slab. Other balls read `y`.
   - So `z` is locally legal. `Δ(y, z)` is two nonempty pieces at distance `> 2D`, which contradicts
     Lemma 1′.
   - Two extensions that vary in different single branches are handled by applying the same argument
     to that pair.
2. **Nesting.**
   - `M_r ⊆ M_(r+1)`, so `E_(r+1)(x) ⊆ E_r(x)` and `V_(r+1) ⊆ V_r`.
   - For `S = B_r`, the components are the subtrees hanging at the vertices of the sphere of radius
     `r+1`. Item 1 puts `V_r` in one of them, and `V_(r+1) ≠ ∅` puts it in a subtree at level `r+1`
     inside the level-`r` one.
   - The intersection of the nested subtrees is one end `ξ(x)`.

   **Independence of the centre.**
   - Slabs about `c` are sandwiched between slabs about `1`, because
     `B_(r-|c|)(1) ⊆ B_r(c) ⊆ B_(r+|c|)(1)`.
   - So tightness does not depend on the centre, and neither does the end.
   - Hence `ξ(λ.x) = ξ(x)` for `λ ∈ Λ_0`, since slabs are `Λ_0`-invariant, and
     `ξ(h.x) = h ξ(x)` for `h ∈ F_n`.
   - The defining sets of `X_nt` and `ξ` are analytic (projections of Borel sets), so they are
     measurable for every Borel probability measure, which is all item 3 uses.
3. `ξ_*(μ|X_nt)` is an `F_n`-invariant finite measure on `∂T`. For `n >= 2` there is none except `0`
   (standard, recalled: ping-pong).
4. With `Λ_0` trivial, the slab is the finite ball `B_(R+w)`, and `E_R(x)` is the cylinder of `x` on it.
   - (a) So tight at some scale means isolated.
   - (b) **Continuity.** Let `x` be non-isolated. Every cylinder `C` of `x` at level `r` has at least
     two points, and by item 1 its points agree off one deep branch. That branch is a function of `C`,
     so the level-`r` subtree containing `ξ` is locally constant, and `ξ` is continuous. The action of
     `F_n` on `∂T` is topologically amenable (standard, recalled). A continuous equivariant map to an
     amenable action makes the source amenable: pull the approximately invariant maps back along `ξ`.
   - (c) By item 3 and (a), `μ` is carried by the countable set of isolated points, so it is atomic.
     An invariant atomic probability measure charges only finite orbits. ∎

## Calibration

- **End shift of `F_n`.** No point is tight: fixing the arrows on a ball leaves the end free inside one
  shadow. `X_nt = X`, and `ξ` is the coded end. There is no invariant measure, and `ξ` is the continuous factor map of item 4(b).
- **`∂T_m ⊠ ∂T_n` over `F_m × F_n`** (take `Λ_0 = F_m`). A slab fixes the first end and leaves the
  second free in one branch, so `X_nt = X`. There is no invariant measure. Both are consistent.
- **Periodic SFTs over `F_n`** (colourings by a finite quotient). They are rigid and tight, and their
  invariant measures live on the finite orbit. This is consistent with item 4.
- **Mozes-type homogeneous spaces.** They carry an invariant probability measure and are nowhere tight,
  so item 3 forbids rigidity. This is proved directly in
  `tree-lattice-homogeneous-subshifts-are-not-quantum-rigid`.

## Lesson for general BH

**Over a free factor, rigidity produces its own boundary.**
- The free branches of nested slabs converge to an end.
- That end is exactly the compression end of `free-group-boundary-shifts-are-quantum-rigid`, recovered
  from rigidity alone.
- So a rigid subshift is, off its tight part, a measurable extension of `∂F_n`, and an invariant
  measure must live on the tight part.

**For the master route.** Non-amenable dynamics with an invariant measure can be rigid over
`Λ_0 × F_n` only as a *tight spacetime*: the whole configuration is a function of one thick slab.
- That is the one place left to look for a measure-preserving counterexample to (RA) over such groups.
- Over `F_n` itself, (RA) is a theorem: every rigid subshift without isolated points factors continuously onto `∂F_n`.
