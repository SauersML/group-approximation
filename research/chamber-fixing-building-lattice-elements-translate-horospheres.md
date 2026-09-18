---
rg: 2
id: chamber-fixing-building-lattice-elements-translate-horospheres
kind: claim
title: In a torsion-free discrete group of type-preserving automorphisms of a Euclidean building, every nontrivial element fixing a chamber at infinity has nonzero vector Busemann translation at that chamber
distinct_from:
  euclidean-building-boundary-shifts-are-quantum-rigid: that notes the boundary shift is only topologically free because periodic-flat elements fix chambers at infinity; this measures exactly how those elements fail to be free, by a nonzero lattice-valued translation, which is what a Z^r-decorated fibre can detect.
  busemann-null-isometries-have-no-boundary-contraction: that is about Busemann-null isometries and boundary contraction; this is the lattice-valued chamber Busemann cocycle of a building and its kernel on chamber stabilizers.
---

**ESTABLISHED** by the proof below (lane bh-invent-04, 2026-09-18; elementary; not reviewed; no
priority claimed, as this is likely folklore). It uses only standard facts on sectors and
retractions centred at chambers at infinity (Abramenko–Brown, *Buildings*, §11.5–11.7,
recalled, not re-read).

## Statement

Let `Δ` be a locally finite Euclidean building of rank `r`, and `Γ ≤ Aut(Δ)` a torsion-free discrete
group of type-preserving automorphisms. Let `Ω` be the set of chambers at infinity.

1. **Busemann cocycle.** Fix `c ∈ Ω`, an apartment `A` containing a sector in the class `c`, and the
   retraction `ρ = ρ_{A,c}` onto `A` centred at `c`. Write `b_c(x) ∈ R^r` for the coordinates of `ρ(x)` in
   `A`, with the positive Weyl cone `C̄` pointing to `c`. For every `γ ∈ Stab_Γ(c)` there is a vector
   `τ_c(γ)` with `b_c(γx) = b_c(x) + τ_c(γ)` for all `x`. It lies in the translation lattice `L` of
   special vertices of a fixed type, and `γ ↦ τ_c(γ)` is a homomorphism `Stab_Γ(c) → L`.
2. **Main claim.** `τ_c` is injective: if `γ ≠ 1` fixes `c`, then `τ_c(γ) ≠ 0`.

## Proof

1. **Cocycle.** `ρ∘γ` is the retraction centred at `c` onto `γ^{-1}A`, followed by the isomorphism
   `γ: γ^{-1}A → A`. Two retractions centred at `c`, onto apartments `A` and `A'` containing `c`-sectors,
   differ by the unique isomorphism `A' → A` fixing `A ∩ A'`, which contains a `c`-subsector. So
   `ρ∘γ = φ∘ρ`, where `φ` is a type-preserving automorphism of `A` fixing the chamber `c` of `∂A`,
   i.e. a translation. Translations preserving types of special vertices form `L`. Additivity is
   `φ_{γδ} = φ_γ φ_δ`.
2. **Kernel.** Suppose `γ` fixes `c` and `τ_c(γ) = 0`, so `ρ(γx) = ρ(x)` for every `x`.
   - Choose `A ⊇ Q(o, c)` for a special vertex `o`. Then `ρ` is the identity on `Q(o,c)`.
   - The sectors `Q(o,c)` and `γQ(o,c) = Q(γo, c)` lie in the same parallel class, so they contain a
     common subsector `Q(u, c)`. Here `u` is a special vertex (standard).
   - Now `u ∈ Q(γo,c)`, so `γ^{-1}u ∈ Q(o,c)`. Then `ρ(γ^{-1}u) = ρ(γ γ^{-1} u) = ρ(u)`, using `τ = 0`.
   - Both `u` and `γ^{-1}u` lie in `Q(o,c) ⊂ A`, where `ρ` is the identity. Hence `γ^{-1}u = u`.
   - So `γ` fixes a vertex. `Γ` is discrete, so vertex stabilizers are finite; `Γ` is torsion-free, so
     they are trivial. Hence `γ = 1`. ∎

## Consequences

- **Free fibres.** Let `L` act on a space `Y` by `z·y = σ^z y`. The Busemann skew product
  `Γ ↷ Ω ×_β Y` is free if and only if no point of `Y` is fixed by a nonzero `τ_c(γ)`. Here
  `γ·(c, y) = (γc, σ^{β(γ,c)} y)` with `β` the Busemann cocycle `β(γ, c) = b_{γc}(γx) − b_c(x)`, which is
  independent of `x` up to the normalisation. In particular the skew product is free whenever `Y` has no
  periodic points at all.
- **Sharpness.** Conversely, suppose some `γ ≠ 1` stabilizes an apartment `A'` and translates it by `τ`
  (a periodic flat). This holds for cocompact `Γ` in rank 2 (Ballmann–Brin, recalled). Then `γ` fixes
  every `c ∈ ∂A'`, and `γ^N` fixes `(c, y)` for any `y` with a period in `N·τ_c(γ)`. So if `Y` has any
  periodic point, the skew product is not free.
- `busemann-transplants-give-free-sfts-on-building-lattices` uses this to put strongly aperiodic
  `Z^r`-decorations on building lattices.

## Lesson for general BH

- The only non-freeness of a building lattice's boundary action is a **lattice-valued translation**.
  Chamber stabilizers embed in `Z^r` through `τ_c`. So one `Z^r`-coordinate carried along the boundary
  (a "Busemann fibre") detects every stabilizer element.
- For gate G2 this turns "free SFT over a Kazhdan, one-ended, non-amenable building lattice" into a
  question about `Z^r`-subshifts: the fibre must be strongly aperiodic.
