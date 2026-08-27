import GroupApproximation.Analysis.MaximalGroupCStar

/-!
# The universal property of `Cmax(H)` for a target in any universe

Proof-ledger rows `PRE.19` and `MC.02`.  The proposition labelled
`prop:maximal-cstar` in `non_mf_groups_exist.tex` (navigate by the label; the
file is under concurrent edit) now reads

> The canonical map `h ↦ u_h` is injective, and for every unital C*-algebra
> `B` and every homomorphism `ρ : H → U(B)`, there is a unique unital
> *-homomorphism `Cmax(H) → B` with `u_h ↦ ρ(h)` for every `h ∈ H`.

The universe qualification the earlier revision carried — *"lying in a fixed
universe that contains `H`"* — has been deleted, so the printed quantifier
ranges over every unital C*-algebra, in every universe.
`Analysis/MaximalGroupCStar.manuscriptUniverseRelativeMaximalGroupCStar`
quantifies over `B : Type u` at the universe of `H`, and therefore
under-certifies the print.

This file supplies what is provable without a new construction, and states
precisely what is not.

## What is proved here, unconditionally and at every universe

`maximalGroupCStar_lift_unique`: **uniqueness holds for a target in any
universe.**  This is the printed word *unique*, in full generality.  Its
proof is the printed one — *"uniqueness follows from density of `ℂ[H]`"* —
and density is a statement about the source, so nothing in it sees the
universe of `B`: two continuous `*`-homomorphisms out of the topological
closure of `StarAlgebra.adjoin ℂ {u_h}` that agree on the `u_h` agree
everywhere.

`maximalGroupCStar_existsUnique_lift_of_factors`: **existence and uniqueness
for a target in any universe, whenever `ρ` factors through the unitary group
of a C*-algebra at the universe of `H`.**  The factoring datum is a
C*-algebra `B₀ : Type u`, a homomorphism `ρ₀ : H → U(B₀)`, and a unital
`*`-homomorphism `j : B₀ → B` with `j ∘ ρ₀ = ρ`; no injectivity, no
isometry, and no continuity of `j` is required, because the lift is
`j ∘ (lift ρ₀)` and uniqueness is already unconditional.  Taking `B₀ = B`,
`ρ₀ = ρ`, `j = id` recovers `maximalGroupCStar_existsUnique_lift`, so this is
a strict generalization of the same-universe statement.

`manuscriptMaximalGroupCStarAnyUniverse` packages both together with the
injectivity clause.

## What is not proved here, and why

Existence for a target with **no** same-universe factorization is open in
this development.  The construction of `Cmax(H)` in
`Analysis/MaximalGroupCStar` is a bounded product indexed by
`CStarUnitaryRepresentation H`, whose carriers are required to lie in
`Type u`; a representation on `B : Type v` is a coordinate of that product
only after `C*(ρ(H)) ⊆ B` is modelled at `Type u`.  Two routes to such a
model are visible and both need machinery this repository does not have:

* a **GNS route** — every cyclic representation of `ℂ[H]` is the GNS
  representation of a positive-definite function on `H`, which is built from
  `H` alone and so lives at `Type u`.  This is exactly the argument
  `Kazhdan/KazhdanUniverse.IsKazhdanPair.liftUniverse` runs for *real
  orthogonal* representations, using `Kazhdan/KazhdanGNS`.  Carrying it to
  C*-algebras needs the complex GNS construction from a state together with
  the norm formula `‖a‖² = sup_φ φ(a* a)`, i.e. the existence of a
  norm-attaining state.  Mathlib's `Analysis/CStarAlgebra/GelfandNaimarkSegal`
  builds `f.GNS` as `UniformSpace.Completion f.PreGNS` with
  `f.PreGNS := A`, so it stays in the universe of `A` and does not descend;
  it also proves no faithfulness statement (its own `TODO` still lists the
  cyclic vector).
* a **smallness route** — `C*(ρ(H))` is the closure of the image of
  `MonoidAlgebra ℂ H : Type u`, hence has a `Small.{u}` carrier once one
  knows that the closure of a small set in a metric space is small; but
  transporting the whole `CStarAlgebra` structure along `equivShrink` is not
  available in Mathlib and would have to be built instance by instance.

Neither is attempted here rather than half-attempted: an existence statement
carrying a placeholder hypothesis would be exactly the conditional result the
doctrine forbids.  The factorization form above is the sharpest *complete*
statement, and `maximalGroupCStar_lift_unique` closes the uniqueness half of
the printed proposition outright.
-/

namespace GroupApproximation

open scoped CStarAlgebra

noncomputable section

universe u v

variable (G : Type u) [Group G]

/-- **Uniqueness at every universe.**  Two `*`-homomorphisms out of the
maximal group C*-algebra that agree on the canonical generators are equal,
with no restriction on the universe of the target.

This is the printed *"uniqueness follows from density of `ℂ[H]`"*: the
generators generate a dense `*`-subalgebra, and a `*`-homomorphism between
C*-algebras is continuous. -/
theorem maximalGroupCStar_lift_unique {B : Type v} [CStarAlgebra B]
    (f₁ f₂ : MaximalGroupCStar G →⋆ₐ[ℂ] B)
    (h : ∀ g : G, f₁ (maximalGroupCStarGenerator G g)
      = f₂ (maximalGroupCStarGenerator G g)) :
    f₁ = f₂ := by
  apply StarAlgHom.ext_topologicalClosure
      (R := ℂ) (A := MaximalGroupCStarAmbient G) (B := B)
      (map_continuous f₁) (map_continuous f₂)
  apply StarAlgHom.ext_adjoin
  intro x hx
  obtain ⟨g, hg⟩ := hx
  have hx' : x =
      ⟨(maximalGroupCStarAmbientRepresentation G g :
        MaximalGroupCStarAmbient G),
        StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩⟩ := by
    apply Subtype.ext
    exact hg.symm
  rw [hx']
  exact h g

/-- **The universal property at every universe, for a factoring
representation.**  If `ρ : G → U(B)` with `B` in an arbitrary universe
factors as `j ∘ ρ₀` through the unitary group of a C*-algebra `B₀` at the
universe of `G`, then `ρ` extends uniquely across the canonical generators.

Existence is `j` composed with the same-universe lift of `ρ₀`; uniqueness is
`maximalGroupCStar_lift_unique`, which needs no hypothesis at all.  In
particular `j` is required to be neither injective, nor isometric, nor
continuous. -/
theorem maximalGroupCStar_existsUnique_lift_of_factors
    {B : Type v} [CStarAlgebra B] (rho : G →* unitary B)
    {B₀ : Type u} [CStarAlgebra B₀] (rho₀ : G →* unitary B₀)
    (j : B₀ →⋆ₐ[ℂ] B) (hj : ∀ g : G, j (rho₀ g : B₀) = (rho g : B)) :
    ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
      ∀ g : G, f (maximalGroupCStarGenerator G g) = (rho g : B) := by
  obtain ⟨f₀, hf₀, -⟩ := maximalGroupCStar_existsUnique_lift G rho₀
  refine ⟨j.comp f₀, fun g ↦ ?_, ?_⟩
  · show j (f₀ (maximalGroupCStarGenerator G g)) = (rho g : B)
    rw [hf₀ g]
    exact hj g
  · intro q hq
    refine maximalGroupCStar_lift_unique G q (j.comp f₀) fun g ↦ ?_
    rw [hq g]
    show (rho g : B) = j (f₀ (maximalGroupCStarGenerator G g))
    rw [hf₀ g, hj g]

/-- The same-universe universal property is the case `B₀ = B`, `ρ₀ = ρ`,
`j = id` of the factoring form.  Recorded so that the generalization is
visibly a generalization. -/
theorem maximalGroupCStar_existsUnique_lift_of_factors_self
    {B : Type u} [CStarAlgebra B] (rho : G →* unitary B) :
    ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
      ∀ g : G, f (maximalGroupCStarGenerator G g) = (rho g : B) :=
  maximalGroupCStar_existsUnique_lift_of_factors G rho rho
    (StarAlgHom.id ℂ B) fun _ ↦ rfl

/-- **`prop:maximal-cstar` with the universe clause deleted, as far as it is
proved.**

* the canonical map `h ↦ u_h` is injective;
* for a target in **any** universe there is **at most one** unital
  `*`-homomorphism `Cmax(G) → B` carrying `u_g` to `ρ(g)`;
* for a target in any universe through which `ρ` factors from the universe of
  `G`, that homomorphism exists;
* at the universe of `G` itself, no factoring datum is needed.

The gap between the second and third clauses is exactly the existence
statement discussed in this file's module docstring. -/
theorem manuscriptMaximalGroupCStarAnyUniverse :
    ∀ (G : Type u) [Group G],
      Function.Injective (maximalGroupCStarUnitaryHom G) ∧
      (∀ (B : Type v) [CStarAlgebra B] (rho : G →* unitary B)
          (f₁ f₂ : MaximalGroupCStar G →⋆ₐ[ℂ] B),
          (∀ g : G, f₁ (maximalGroupCStarGenerator G g) = (rho g : B)) →
          (∀ g : G, f₂ (maximalGroupCStarGenerator G g) = (rho g : B)) →
          f₁ = f₂) ∧
      (∀ (B : Type v) [CStarAlgebra B] (rho : G →* unitary B)
          (B₀ : Type u) [CStarAlgebra B₀] (rho₀ : G →* unitary B₀)
          (j : B₀ →⋆ₐ[ℂ] B), (∀ g : G, j (rho₀ g : B₀) = (rho g : B)) →
          ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
            ∀ g : G, f (maximalGroupCStarGenerator G g) = (rho g : B)) ∧
      (∀ (B : Type u) [CStarAlgebra B] (rho : G →* unitary B),
          ∃! f : MaximalGroupCStar G →⋆ₐ[ℂ] B,
            ∀ g : G, f (maximalGroupCStarGenerator G g) = (rho g : B)) := by
  intro G _
  refine ⟨maximalGroupCStarUnitaryHom_injective G, ?_, ?_, ?_⟩
  · intro B _ _ f₁ f₂ h₁ h₂
    exact maximalGroupCStar_lift_unique G f₁ f₂ fun g ↦ by rw [h₁ g, h₂ g]
  · intro B _ rho B₀ _ rho₀ j hj
    exact maximalGroupCStar_existsUnique_lift_of_factors G rho rho₀ j hj
  · intro B _ rho
    exact maximalGroupCStar_existsUnique_lift G rho

end

end GroupApproximation
