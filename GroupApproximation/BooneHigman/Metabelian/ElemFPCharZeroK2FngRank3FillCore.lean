import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Coset-graph filling: the abstract Schreier / height-induction core (lane `bh-met-93z`, part 1)

Let `F = FreeGroup α` act on a set `Y` through a hom `ev : F →* G` and a `G`-action on `Y`.
Fix a base vertex `y₀`, a vertex labelling `σ : Y → F` with `σ y₀ = 1` (a "combing": in the
application `σ y` is a geodesic word from `y₀` to `y` in the Schreier graph) and a height
`ht : Y → ℕ`.  For a letter `a` and a vertex `y` put

* `schGen a y = σ(a • y)⁻¹ · a · σ(y)` (the **Schreier generator** of the edge `y —a→ a • y`),
* `level a y = max (ht y) (ht (a • y))` (the height of that edge),
* `lower n = {schGen b z | level b z < n}` (the edges strictly below height `n`).

**Proved outright (no hypotheses beyond the displayed ones).**
* `czK2FngRank3Fill_mem_of_schGen` (Schreier rewriting): if every Schreier generator lies in a
  subgroup `M`, then every word `w` with `ev w • y₀ = y₀` lies in `M`.  Proof: induction on
  `w` of `σ(w • y)⁻¹ · w · σ(y) ∈ M` for all `y` (telescoping), then `y = y₀`.
* `czK2FngRank3Fill_schGen_mem_of_local` (filling by induction on height): if each Schreier
  generator lies in `M ⊔ ⟨lower (level a y)⟩` (**local filling**), then each lies in `M`.
  Proof: strong induction on the level.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

section Core

variable {α G Y : Type*} [Group G] [MulAction G Y]

/-- The Schreier generator `σ(a • y)⁻¹ · a · σ(y)` of the edge `y —a→ a • y`. -/
def czK2FngRank3Fill_schGen (ev : FreeGroup α →* G) (σ : Y → FreeGroup α) (a : α) (y : Y) :
    FreeGroup α :=
  (σ (ev (FreeGroup.of a) • y))⁻¹ * FreeGroup.of a * σ y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_schGen

/-- The height `max (ht y) (ht (a • y))` of the edge `y —a→ a • y`. -/
def czK2FngRank3Fill_level (ev : FreeGroup α →* G) (ht : Y → ℕ) (a : α) (y : Y) : ℕ :=
  max (ht y) (ht (ev (FreeGroup.of a) • y))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_level

/-- The Schreier generators of the edges of height `< n`. -/
def czK2FngRank3Fill_lower (ev : FreeGroup α →* G) (σ : Y → FreeGroup α) (ht : Y → ℕ)
    (n : ℕ) : Set (FreeGroup α) :=
  {g | ∃ b z, czK2FngRank3Fill_level ev ht b z < n ∧ g = czK2FngRank3Fill_schGen ev σ b z}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_lower

/-- **Telescoping.**  If all Schreier generators lie in `M`, then `σ(w • y)⁻¹ · w · σ(y) ∈ M`
for every word `w` and every vertex `y`. -/
theorem czK2FngRank3Fill_telescope (ev : FreeGroup α →* G) (σ : Y → FreeGroup α)
    (M : Subgroup (FreeGroup α)) (hsch : ∀ a y, czK2FngRank3Fill_schGen ev σ a y ∈ M)
    (w : FreeGroup α) : ∀ y : Y, (σ (ev w • y))⁻¹ * w * σ y ∈ M := by
  refine FreeGroup.induction_on w ?_ (fun x ↦ ?_) (fun x hx ↦ ?_) (fun u v hu hv ↦ ?_)
  · intro y
    rw [map_one, one_smul, mul_one, inv_mul_cancel]
    exact one_mem M
  · exact fun y ↦ hsch x y
  · intro y
    have hz : ev (FreeGroup.of x) • (ev (FreeGroup.of x)⁻¹ • y) = y := by
      rw [map_inv, smul_inv_smul]
    have h' := inv_mem (hx (ev (FreeGroup.of x)⁻¹ • y))
    rw [hz, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc] at h'
    exact h'
  · intro y
    have e : (σ (ev (u * v) • y))⁻¹ * (u * v) * σ y =
        ((σ (ev u • (ev v • y)))⁻¹ * u * σ (ev v • y)) *
          ((σ (ev v • y))⁻¹ * v * σ y) := by
      rw [map_mul, mul_smul]
      group
    rw [e]
    exact mul_mem (hu _) (hv y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_telescope

/-- **Schreier rewriting.**  If every Schreier generator lies in `M` and `σ y₀ = 1`, then every
word fixing `y₀` lies in `M`. -/
theorem czK2FngRank3Fill_mem_of_schGen (ev : FreeGroup α →* G) (y₀ : Y)
    (σ : Y → FreeGroup α) (hσ : σ y₀ = 1) (M : Subgroup (FreeGroup α))
    (hsch : ∀ a y, czK2FngRank3Fill_schGen ev σ a y ∈ M) {w : FreeGroup α}
    (hw : ev w • y₀ = y₀) : w ∈ M := by
  have h := czK2FngRank3Fill_telescope ev σ M hsch w y₀
  rwa [hw, hσ, inv_one, one_mul, mul_one] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_mem_of_schGen

/-- **Filling by induction on height.**  If every Schreier generator lies in
`M ⊔ ⟨lower (level a y)⟩`, then every Schreier generator lies in `M`. -/
theorem czK2FngRank3Fill_schGen_mem_of_local (ev : FreeGroup α →* G) (σ : Y → FreeGroup α)
    (ht : Y → ℕ) (M : Subgroup (FreeGroup α))
    (hloc : ∀ a y, czK2FngRank3Fill_schGen ev σ a y ∈
      M ⊔ Subgroup.closure (czK2FngRank3Fill_lower ev σ ht (czK2FngRank3Fill_level ev ht a y)))
    (a : α) (y : Y) : czK2FngRank3Fill_schGen ev σ a y ∈ M := by
  have key : ∀ n : ℕ, ∀ (a : α) (y : Y), czK2FngRank3Fill_level ev ht a y = n →
      czK2FngRank3Fill_schGen ev σ a y ∈ M := by
    intro n
    refine Nat.strong_induction_on n fun n ih ↦ ?_
    intro a y hn
    have hle : Subgroup.closure
        (czK2FngRank3Fill_lower ev σ ht (czK2FngRank3Fill_level ev ht a y)) ≤ M := by
      rw [Subgroup.closure_le]
      rintro g ⟨b, z, hlt, rfl⟩
      exact ih _ (hlt.trans_eq hn) b z rfl
    exact sup_le le_rfl hle (hloc a y)
  exact key _ a y rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_schGen_mem_of_local

end Core

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
