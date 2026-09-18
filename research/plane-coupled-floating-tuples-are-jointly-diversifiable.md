---
rg: 2
id: plane-coupled-floating-tuples-are-jointly-diversifiable
kind: claim
title: A plane-constant Durand--Romashchenko simulation over Λ_0 x Z^2 can force the data floating on infinite active father-chains to form Y-patterns across planes
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the full lifting statement (M1); this isolates the one step of the plane-constant DR design that is not a routine transcription, namely minimality at the floating locus.
  injective-plane-lift-codings-force-finite-type: that shows a floating locus must exist in every M1 solution; this asks that its content be controllable, i.e. Y-coherent across planes.
  durand-romashchenko-minimal-sft-simulation: that diversifies one floating letter at a time in Z^d with plane-independent slots; this needs tuples of floating letters indexed by Λ_0, coherent with Y, which plane-independent slots cannot produce.
---

**OPEN.** Crux of (M1) after the reduction in its Attempt 2.

**Setting.** `Λ_0` finitely presented with solvable word problem, `Y ⊆ B^{Λ_0}`
effective and minimal but not of finite type, `Λ = Λ_0 x Z^2`. A *plane-constant
DR design* is an SFT `X ⊆ A^Λ` with layers:
- `H`: a DR (Durand--Romashchenko) fixed-point hierarchy on `Z^2`, constant
  along `Λ_0`;
- `L`: a letter layer, constant along each plane `{λ} x Z^2`, giving `Φ`;
- `C`: zone computations that, at level `k` in plane `λ`, hold a table indexed
  by the ball `F_k ⊆ Λ_0`, tied to `L` by cell-wise twin checks between the
  planes `λ` and `λs` (`s` a generator) and checked against the first `k`
  forbidden patterns of `Y`;
- `D`: diversification slots and delegation wires as in DR (fields (iv)--(vi)).

An *infinite active chain* is a cell whose father chain in `H` is infinite and
lies in a computation zone or a wire at every level. There the carried
symbols are not tied to `L` at any finite level. Reading them at a fixed
`Z^2`-position gives a partial configuration `w` over `Λ_0`, the *floating
tuple*.

**Statement.** There is a plane-constant DR design in which, for every
`x ∈ X`, every infinite active chain and every finite `F ⊆ Λ_0`, the floating
tuple restricted to `λF` is a `Y`-pattern (it lies in
`R_F(Y) = { f ↦ y(λ' f) : y ∈ Y, λ' ∈ Λ_0 }`), and each tuple so realised also
occurs at a finite chain of some generic point.

**Payoff.** With the reductions recorded in
`effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`
(Attempt 2: reading pressure dissolved, finite-chain recurrence), this is
expected to give (M1), and so premise (M1) of
`minimal-free-sft-via-plane-constant-minimal-simulation`. That expectation is
not checked in full.

**How it fails.**
- *Local-only constraint (dies).* If the floating tuples range over a
  `Λ_0`-SFT `W` independently of `y`, minimality puts every pattern of `W` in
  the language of `Y`. So `W ⊆ Y`, hence `W = Y` by minimality of `Y`, and `Y`
  is of finite type, against the hypothesis. This is the Barbieri--Sablik
  situation: the degenerate lattice `B_∞` of their Toeplitz encoding holds a
  symbol constrained only by the edge relations. (Sketch. It assumes that
  placing any `w ∈ W` is compatible with every `y`.)
- *Plane-independent slots (die).* DR slots at a given `Z^2`-position have the
  same schedule in every plane, since `H` is `Λ_0`-constant. So the slot
  tuples across planes are constant, `(σ, σ, ..., σ)`, and they cover
  `R_F(Y)` only when `Y` contains constant patterns on `F`.
- *What would work.* A floating tuple that is forced to equal a translate of
  `y` itself, `w(λ) = y(λ g)` for one `g` determined by the degenerate
  hierarchy: a "delegation to infinity" that stays coupled to `L`. No such
  mechanism is known.
