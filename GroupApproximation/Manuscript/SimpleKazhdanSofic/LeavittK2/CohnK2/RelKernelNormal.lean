import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelSwap
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.MatrixUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# Root elements of `(p)` generate a normal subgroup (lane `sk-cohn-02`, module 3)

Write `C = C_2(𝔽₂)`, `u(α, β) = α p β*` and `I = (p)`.  For a finite set `S` of binary words,
`relKer_gens N S` is the set of roots `x_ij(u(α, β))` with `α, β ∈ S`.  Put
`relKer_U N = ⋃_S ⟨relKer_gens N S⟩`.  This is a subgroup, since the closures are directed.

* `relKer_x_mem_U`: `x_ij(a) ∈ U` for every `a ∈ I`.  Over `𝔽₂`, `I` is the span of the
  `u(α, β)` (`CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan`), and `x_ij` is additive.
* `relKer_U_normal`: for `N ≥ 3`, `U` is normal.  A conjugate of a root in `U` by a
  non-opposite root is a product of roots with coefficients in `I`.  For the opposite root,
  write `x_ij(u(α, β)) = ⁅x_im(u(α, β)), x_mj(u(β, β))⁆` with a third index `m`, and use the
  non-opposite case twice.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup
open scoped commutatorElement

local notation "C₂" => CohnTwo (ZMod 2)
local notation "D₂" => CohnTwo.data (ZMod 2)

/-- `c ⁅a, b⁆ c⁻¹ = ⁅c a c⁻¹, c b c⁻¹⁆`. -/
theorem relKer_conj_commutator {G : Type*} [Group G] (c a b : G) :
    c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_conj_commutator

/-- `P X⁻¹ P⁻¹ = (P X P⁻¹)⁻¹`. -/
theorem relKer_grp_conj_inv {G : Type*} [Group G] (P X : G) :
    P * X⁻¹ * P⁻¹ = (P * X * P⁻¹)⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_inv

/-- Conjugation by a product. -/
theorem relKer_grp_conj_conj {G : Type*} [Group G] (c d g : G) :
    c * d * g * (c * d)⁻¹ = c * (d * g * d⁻¹) * c⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_conj

/-- Conjugation by the inverse of a product. -/
theorem relKer_grp_conj_conj' {G : Type*} [Group G] (c d g : G) :
    (c * d)⁻¹ * g * (c * d)⁻¹⁻¹ = d⁻¹ * (c⁻¹ * g * c⁻¹⁻¹) * d⁻¹⁻¹ := by
  group

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_grp_conj_conj'

/-- A subgroup contains the commutator of two of its elements. -/
theorem relKer_commutator_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_commutator_mem

/-- The matrix unit `u(α, β)` lies in `(p)`. -/
theorem relKer_unit_mem (u v : List (Fin 2)) : (D₂).unit u v ∈ CohnTwo.pIdeal (ZMod 2) := by
  have hp : CohnTwo.cohnP (ZMod 2) ∈ CohnTwo.pIdeal (ZMod 2) :=
    TwoSidedIdeal.subset_span (Set.mem_singleton _)
  show (D₂).word u * CohnTwo.cohnP (ZMod 2) * (D₂).coword v ∈ CohnTwo.pIdeal (ZMod 2)
  exact (CohnTwo.pIdeal (ZMod 2)).mul_mem_right _ _
    ((CohnTwo.pIdeal (ZMod 2)).mul_mem_left _ _ hp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_unit_mem

/-- Roots `x_ij(u(α, β))` with `α, β ∈ S`. -/
def relKer_gens (N : ℕ) (S : Finset (List (Fin 2))) : Set (SteinbergGroup (Fin N) C₂) :=
  {g | ∃ (i j : Fin N) (hij : i ≠ j) (u v : List (Fin 2)), u ∈ S ∧ v ∈ S ∧
    g = x i j hij ((D₂).unit u v)}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_gens

theorem relKer_gens_mono (N : ℕ) {S T : Finset (List (Fin 2))} (h : S ⊆ T) :
    relKer_gens N S ⊆ relKer_gens N T := by
  rintro g ⟨i, j, hij, u, v, hu, hv, rfl⟩
  exact ⟨i, j, hij, u, v, h hu, h hv, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_gens_mono

/-- The directed union `U = ⋃_S ⟨relKer_gens N S⟩`. -/
def relKer_U (N : ℕ) : Subgroup (SteinbergGroup (Fin N) C₂) where
  carrier := {g | ∃ S : Finset (List (Fin 2)), g ∈ Subgroup.closure (relKer_gens N S)}
  one_mem' := ⟨∅, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨S, hS⟩ ⟨T, hT⟩
    exact ⟨S ∪ T, Subgroup.mul_mem _
      (Subgroup.closure_mono (relKer_gens_mono N Finset.subset_union_left) hS)
      (Subgroup.closure_mono (relKer_gens_mono N Finset.subset_union_right) hT)⟩
  inv_mem' := by
    rintro a ⟨S, hS⟩
    exact ⟨S, Subgroup.inv_mem _ hS⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_U

theorem relKer_mem_U_iff (N : ℕ) (g : SteinbergGroup (Fin N) C₂) :
    g ∈ relKer_U N ↔ ∃ S : Finset (List (Fin 2)), g ∈ Subgroup.closure (relKer_gens N S) :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_mem_U_iff

/-- Every root with coefficient in `(p)` lies in `U`. -/
theorem relKer_x_mem_U (N : ℕ) (i j : Fin N) (hij : i ≠ j) (a : C₂)
    (ha : a ∈ CohnTwo.pIdeal (ZMod 2)) : x i j hij a ∈ relKer_U N := by
  rw [CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan, CohnTwo.matrixUnitSpan] at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨⟨u, v⟩, rfl⟩ := hy
      exact (relKer_mem_U_iff N _).mpr ⟨{u, v}, Subgroup.subset_closure
        ⟨i, j, hij, u, v, Finset.mem_insert_self u {v},
          Finset.mem_insert_of_mem (Finset.mem_singleton_self v), rfl⟩⟩
  | zero => rw [x_zero]; exact (relKer_U N).one_mem
  | add y z _ _ hy hz => rw [← x_mul]; exact (relKer_U N).mul_mem hy hz
  | smul c y _ hy =>
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with h | h
      · rw [h, zero_smul, x_zero]; exact (relKer_U N).one_mem
      · rw [h, one_smul]; exact hy

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_x_mem_U

/-- A third index. -/
theorem relKer_third {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) : ∃ m : Fin N, m ≠ i ∧ m ≠ j := by
  have ht : ∃ t : ℕ, t < 3 ∧ t ≠ i.val ∧ t ≠ j.val := by
    by_cases h0 : 0 ≠ i.val ∧ 0 ≠ j.val
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i.val ∧ 1 ≠ j.val
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨t, ht3, hti, htj⟩ := ht
  exact ⟨⟨t, by omega⟩, fun h => hti (congrArg Fin.val h), fun h => htj (congrArg Fin.val h)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_third
