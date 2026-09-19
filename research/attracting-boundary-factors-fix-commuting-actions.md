---
rg: 2
id: attracting-boundary-factors-fix-commuting-actions
kind: claim
title: A minimal system with a dense-basin attracting point receives at most one factor map from each minimal system, so commuting actions fix it pointwise and its finite-to-one extensions have finite automorphism groups; the compression-rigid scaffolds carry only finite time
distinct_from:
  deterministic-time-lifts-inherit-quantum-rigidity: that proves a time lift inherits rigidity from its row SFT; this bounds which time groups a row can carry at all, and the bound is finite for every boundary-type row.
  time-lift-actors-carry-no-complexity-beyond-row-language: that bounds the word problem of a time group by the row language; this bounds its cardinality by the row's boundary fibres, independently of any language.
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that says a folded SFT is rigid only if its fibre is; this says where the input acts in any product design, namely inside the fibres over the other factor's boundary.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that builds a rigid minimal topologically free SFT over an Ã₂ lattice; this shows its automorphism group has order at most the phase group, so it cannot be the row of a time lift carrying an infinite input.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-18; elementary; not independently reviewed).
The core lemma is a dense-basin variant of classical facts: factor maps onto minimal proximal flows
are unique, and such flows have trivial automorphism group (Glasner, *Proximal flows*, LNM 517,
1976; recalled, not re-read). No priority is claimed for Theorem A. The corollaries for the master
route are the point of this node.

## Setting

A countable group `Γ` acts by homeomorphisms on a compact metrizable space. An **attractor** of a
`Γ`-system `Ω` is a pair `(a, c₊)` with `a ∈ Γ`, `c₊ ∈ Ω`, and **basin**
`B = {c : aⁿc -> c₊}` containing an open dense set. No uniformity is assumed.
`Aut_Γ(Y)` is the group of homeomorphisms of `Y` commuting with `Γ`.

## Statement

**Theorem A.** Let `Ω` be a minimal `Γ`-system with an attractor, and `Y` a minimal `Γ`-system.
Any two factor maps `π₁, π₂ : Y -> Ω` are equal.

**Corollary B.** In the setting of Theorem A:
1. `Aut_Γ(Ω) = 1`.
2. If `π : Y -> Ω` is a factor map, then every `α ∈ Aut_Γ(Y)` satisfies `π∘α = π`, and
   `α ≠ id` has no fixed point. So `|Aut_Γ(Y)| ≤ |π⁻¹(ω)|` for every `ω ∈ Ω`, and a
   finite-to-one extension of `Ω` has a finite automorphism group.

**Corollary C (commuting factors).** Let `Λ = Λ₁ × Λ₂` act on a compact `X`, and let `Ω` be a
`Λ`-factor of `X` on which `Λ₂` acts minimally with an attractor. Then `Λ₁` acts trivially on `Ω`.
So every fibre `π⁻¹(ω)` is invariant under `Λ₁ × Stab_(Λ₂)(ω)`.

**Corollary D (time lifts).** In the setting of `deterministic-time-lifts-inherit-quantum-rigidity`,
suppose the row SFT `Y` over `Λ₂` is minimal and has a factor map onto a minimal `Λ₂`-system
with an attractor, with some fibre of size `N < ∞`. Then `|Φ(Λ₁)| ≤ N`. The lift is faithful only
if `Λ₁` is finite of order at most `N`.

**Instances.** Each of these rows has an automorphism group of the order shown, and each is the row
of a time lift only for finite time groups of at most that order.
1. The boundary shift of `F_d`, `d ≥ 2` (`free-group-boundary-shift-is-quantum-rigid`): `1`.
2. The boundary products over `F_m × F_n` (`free-group-boundary-shifts-are-quantum-rigid`): `1`.
3. The Ã₂ skew shifts `P` of `a2-lattice-boundary-skew-shifts-are-quantum-rigid`: at most `|Φ|`,
   the order of the finite phase group.
4. Any minimal SFT over a non-elementary hyperbolic group with a finite-to-one factor map onto
   the Gromov boundary: at most the minimal fibre size.

**Contrast.** Over an abelian group (in particular `Z^d`), no nontrivial minimal system has an
attractor, so the bound is vacuous there. That is where the time-lift designs have lived.

## Proof

**Lemma (semi-openness).** A factor map `π : Y -> Ω` from a minimal system pulls open dense sets
back to open dense sets.
- Let `U ⊆ Y` be nonempty and open, and pick a nonempty open `V` with `V̄ ⊆ U`.
- The union of the translates of `V` is open, invariant and nonempty, so by minimality it is all of
  `Y`. By compactness, `Y = γ₁V ∪ … ∪ γ_kV`.
- So `Ω = γ₁π(V̄) ∪ … ∪ γ_kπ(V̄)`, a finite union of closed sets. By Baire one of them has
  nonempty interior, so `π(U) ⊇ π(V̄)` has nonempty interior.
- If `D ⊆ Ω` is open and dense, then `π(U)` meets `D`, so `U` meets `π⁻¹(D)`.

**Theorem A.**
- Let `D ⊆ B` be open and dense. By the lemma, `π₁⁻¹(D) ∩ π₂⁻¹(D)` is open and dense, so it
  contains some `y`.
- The map `z ↦ (π₁z, π₂z)` is equivariant, so its image `M ⊆ Ω × Ω` is a closed minimal set.
- `aⁿ(π₁y, π₂y) = (aⁿπ₁y, aⁿπ₂y) -> (c₊, c₊)`, and `M` is closed, so `(c₊, c₊) ∈ M`.
- By minimality, `M` is the orbit closure of `(c₊, c₊)`, which lies in the diagonal. So
  `π₁ = π₂`.

**Corollary B.**
1. Apply Theorem A to `π₁ = id` and `π₂ = α`.
2. `π∘α` is a factor map, so `π∘α = π` by Theorem A. `Fix(α)` is closed and `Γ`-invariant, so it is
   empty or `Y`. Hence for fixed `y`, the map `α ↦ α(y)` is injective and lands in `π⁻¹(π(y))`.

**Corollary C.** Each `(λ, 1)` with `λ ∈ Λ₁` commutes with `1 × Λ₂`, so its action on `Ω` lies in
`Aut_(Λ₂)(Ω)`, which is trivial by B.1.

**Corollary D.** By item 1 of the time-lift node, `(X, Λ)` is conjugate to `Y` with `Λ₁` acting
through `Φ : Λ₁ -> Aut_(Λ₂)(Y)`. Apply B.2. The kernel of `Φ` acts trivially on `X`.

**Instances.**
1. For `a ≠ 1` in `F_d`, `aⁿξ -> a^(+∞)` for every end `ξ ≠ a^(−∞)`. The boundary action is
   minimal, and the boundary shift is conjugate to it.
2. For `(a, b)` with `a, b ≠ 1`, the basin contains `(∂F_m ∖ {a^(−∞)}) × (∂F_n ∖ {b^(−∞)})`,
   which is open and dense. The product action is minimal.
3. **Setup.** `Γ ↷ Ω` is minimal (Step 5.4 of `a2-lattices-embed-in-fp-simple-groups`, used in
   the skew-shift node). Let `Γ₀` be the type-preserving subgroup, of index at most 3; it acts
   cocompactly. It contains a strongly regular hyperbolic `a` (Caprace–Ciobotaru,
   arXiv:1304.6210, Theorem 1.2, as pinned in the opposition-proximal node).
   - **Attractor.** Part (a) of `strongly-regular-building-elements-are-opposition-proximal` makes
     `O(c₋)` open and dense. Part (b) gives `aⁿc -> c₊` on it. Both are in the cone topology,
     which is the sector topology of the host node (standard; recalled).
   - **Conclusion.** So `(a, c₊)` is an attractor of the minimal `Γ`-system `Ω`, with
     `a ∈ Γ₀ ⊆ Γ`. `P` is minimal (item 1 of the skew-shift node), and `P -> Ω` is a factor map
     with fibres of size at most `|Φ|`. Apply B.2 to `Γ`.
4. Loxodromic elements have north–south dynamics on the Gromov boundary, and the boundary action is
   minimal (standard; recalled).

**Contrast.** Let `(a, c₊)` be an attractor with `a` central. Then:
- `ac₊ = c₊`;
- `Fix(a)` is closed and `Γ`-invariant, so it is all of `Ω`;
- so `aⁿc = c` for all `c`, and the basin is `{c₊}`;
- by density, `Ω = {c₊}`.

## Consequences for the master route

1. **The input never sees the other factor's boundary.** In a Track A design over
   `Λ = Λ₁ × Λ₂`, with the input in `Λ₁`, Corollary C makes every boundary-type factor of the
   `Λ₂`-action `Λ₁`-invariant pointwise. Rigidity that `Λ₂` supplies by compression reaches only
   coordinates that the input does not move.
2. **The input acts inside fibres, over an abelian stabilizer.** The input's coordinates live in the
   fibres `π⁻¹(ω)`, and the elements of `Λ` preserving a fibre form `Λ₁ × Stab_(Λ₂)(ω)`.
   - **Building lattices.** If `Λ₂` is a torsion-free type-preserving lattice of a Euclidean
     building and `Ω` is its chamber boundary, then
     `chamber-fixing-building-lattice-elements-translate-horospheres` makes the Busemann
     homomorphism `Stab(ω) -> Z^r` injective.
   - **Free groups.** For `F_n`, `Stab(ξ)` is trivial or cyclic.
   - **The consequence.** Every fibre-by-fibre argument for the input's coordinates runs over
     `Λ₁ × (a subgroup of Z^r)`. Geometric scaffolds hand the input's rigidity problem back in
     `Λ₁ × Z^r` form, the shape of the `Z²` gate. This is the dynamical counterpart of the fold
     lemma.
3. **No time over compression scaffolds.** By Corollary D and Instances 1–4, the time-lift design
   (rule 8) cannot use any compression-rigid row built so far to carry an infinite input. This is
   independent of the language bound in `time-lift-actors-carry-no-complexity-beyond-row-language`.
   Programmable time needs rigid rows whose boundary fibres are infinite, which means rigidity of the
   non-proximal part. Over `Z^d` there is no proximal part, which is why rule 8 lives on `Z²` rows.

## What this leaves

- **Geometric scaffolds are exhausted as carriers of the input.** Rigidity from boundary geometry
  (rank one, products, Ã₂ via finite presentation) supplies neither time nor fibre rigidity. The
  input's coordinates must be rigidified over `Λ₁ × Z^r` or by `Λ₁`'s own geometry.
- **The symbolic-free alternative.** The permutational route
  (`type-a-action-gives-boone-higman-for-subgroups`) replaces gates E1–E3 with a single gate: an
  fp overgroup with a type (A) action.
  - **Labels do not help.** Let `LC(C, K) ⋊ V` act on `T × D` by
    `(f, v)·(t, x) = (f(vx)·t, vx)`. A pair in one fibre goes to a pair in one fibre, moved by a
    single `k ∈ K`. So this action has infinitely many orbits on pairs whenever `K ↷ T` does.
    Labels over a Thompson base cannot manufacture type (A); the compiler must act on the input's
    own points.

## Lesson for general BH

**Attractors fix everything that commutes with them.** One element with a dense-basin attracting
point makes factor maps onto a minimal system unique. So a product factor or time direction
commuting with a boundary-type action fixes that boundary pointwise, and moves only fibres whose
stabilizers are abelian, of rank at most `r` for building lattices.
- **Compression rigidity is proximal.** It rigidifies what the input cannot touch.
- **The dichotomy.** Every geometric route returns the input's problem as a `Λ₁ × Z^r` problem,
  that is, the `Z²` gate. Any route avoiding that gate must give the input type (A) on its own
  points.
