import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDiagonalize

/-!
# Connes' trick: the layered model of Connes' trick

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick).
Adapted from the never-wired foreign `TWWLanes/ConnesTrick` module of the same content.

Take a model `B : A → M_Y` in the eigenbasis of the density, and multiplicities `c : Y → ℕ`.
Connes' trick uses the new model on `Σ i : Y, Fin (c i)`, which has `c i` copies of the basis
vector `i`:

`layer c M ⟨i, a⟩ ⟨j, b⟩ = if a = b then M i j else 0`.

If `E_k = span {i : k < c i}`, then `layer c M` is the direct sum over `k` of the compressions
`E_k M E_k`. The layer-`k` isometry is `layerVec c k`, and

`layer c M = ∑ₖ (layerVec c k)ᴴ M (layerVec c k)`   (`layer_eq_sum_conj`).

So `layer c` is unital (`layer_one`), `ℂ`-linear (`layerLinear`), and a sum of compressions.
Composing it with a ucp model therefore gives a ucp model (`layerLinear_comp_ucp`), by
`isCompletelyPositiveOnMatrices_sum_conj`. Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] {Y : FiniteModel}

/-- The layered model: `c i` copies of each basis vector `i`. -/
abbrev layerModel (Y : FiniteModel) (c : Y → ℕ) : FiniteModel :=
  ⟨(Σ i : Y, Fin (c i)), inferInstance, inferInstance⟩

/-- The layered matrix `⊕ₖ E_k M E_k`. -/
def layer (c : Y → ℕ) (M : Matrix Y Y ℂ) : Matrix (layerModel Y c) (layerModel Y c) ℂ :=
  Matrix.of fun p q ↦ if (p.2 : ℕ) = (q.2 : ℕ) then M p.1 q.1 else 0

theorem layer_apply (c : Y → ℕ) (M : Matrix Y Y ℂ) (p q : layerModel Y c) :
    layer c M p q = if (p.2 : ℕ) = (q.2 : ℕ) then M p.1 q.1 else 0 := rfl

/-- The isometry onto layer `k`. Its columns are the basis vectors `i` with `k < c i`. -/
def layerVec (c : Y → ℕ) (k : ℕ) : Matrix Y (layerModel Y c) ℂ :=
  Matrix.of fun y p ↦ if y = p.1 ∧ (p.2 : ℕ) = k then 1 else 0

/-- The entries of the layer-`k` compression. -/
theorem layerVec_conj_apply (c : Y → ℕ) (k : ℕ) (M : Matrix Y Y ℂ) (p q : layerModel Y c) :
    ((layerVec c k)ᴴ * M * layerVec c k) p q
      = if (p.2 : ℕ) = k ∧ (q.2 : ℕ) = k then M p.1 q.1 else 0 := by
  have hL : ∀ z : Y, (layerVec c k)ᴴ p z = if z = p.1 ∧ (p.2 : ℕ) = k then 1 else 0 :=
    fun z ↦ by
      rw [Matrix.conjTranspose_apply]
      simp only [layerVec, Matrix.of_apply]
      split_ifs <;> simp
  simp only [Matrix.mul_apply, hL]
  simp only [layerVec, Matrix.of_apply]
  by_cases hp : (p.2 : ℕ) = k <;> by_cases hq : (q.2 : ℕ) = k <;>
    simp [hp, hq]

/-- Two points of the layered model are equal if and only if their base points are equal and
their layers are equal. -/
theorem layerModel_eq_iff (c : Y → ℕ) (p q : layerModel Y c) :
    p = q ↔ p.1 = q.1 ∧ (p.2 : ℕ) = (q.2 : ℕ) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    rintro ⟨h1, h2⟩
    change i = j at h1
    subst h1
    change (a : ℕ) = (b : ℕ) at h2
    rw [Fin.ext h2]

/-- The layered model is unital. -/
theorem layer_one (c : Y → ℕ) : layer c (1 : Matrix Y Y ℂ) = 1 := by
  ext p q
  rw [layer_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : p = q
  · subst h
    simp
  · have h' : ¬ (p.1 = q.1 ∧ (p.2 : ℕ) = (q.2 : ℕ)) := fun h' ↦
      h ((layerModel_eq_iff c p q).2 h')
    by_cases h2 : (p.2 : ℕ) = (q.2 : ℕ)
    · rw [if_pos h2, if_neg (fun h1 ↦ h' ⟨h1, h2⟩), if_neg h]
    · rw [if_neg h2, if_neg h]

/-- **The layered model is a sum of compressions.** Only the layers `k < ∑ᵢ cᵢ` occur. -/
theorem layer_eq_sum_conj (c : Y → ℕ) (M : Matrix Y Y ℂ) :
    layer c M = ∑ k : Fin (∑ i, c i), (layerVec c (k : ℕ))ᴴ * M * layerVec c (k : ℕ) := by
  ext p q
  rw [layer_apply, Matrix.sum_apply]
  simp only [layerVec_conj_apply]
  have hp : (p.2 : ℕ) < ∑ i, c i :=
    lt_of_lt_of_le p.2.2
      (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (c i)) (Finset.mem_univ p.1))
  rw [Finset.sum_eq_single (⟨p.2, hp⟩ : Fin (∑ i, c i))]
  · by_cases h : (p.2 : ℕ) = (q.2 : ℕ)
    · have hc : (p.2 : ℕ) = ((⟨p.2, hp⟩ : Fin (∑ i, c i)) : ℕ) ∧
          (q.2 : ℕ) = ((⟨p.2, hp⟩ : Fin (∑ i, c i)) : ℕ) := ⟨rfl, h.symm⟩
      rw [if_pos h, if_pos hc]
    · have hc : ¬ ((p.2 : ℕ) = ((⟨p.2, hp⟩ : Fin (∑ i, c i)) : ℕ) ∧
          (q.2 : ℕ) = ((⟨p.2, hp⟩ : Fin (∑ i, c i)) : ℕ)) := fun h' ↦
        h (h'.1.trans h'.2.symm)
      rw [if_neg h, if_neg hc]
  · intro k _ hk
    exact if_neg fun h' ↦ hk (Fin.ext h'.1.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The layered model as a `ℂ`-linear map. -/
def layerLinear (c : Y → ℕ) :
    Matrix Y Y ℂ →ₗ[ℂ] Matrix (layerModel Y c) (layerModel Y c) ℂ where
  toFun := layer c
  map_add' M N := by
    ext p q
    simp only [layer_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' a M := by
    ext p q
    simp only [layer_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem layerLinear_apply (c : Y → ℕ) (M : Matrix Y Y ℂ) : layerLinear c M = layer c M := rfl

/-- **The layered model of a ucp model is a ucp model.** -/
theorem layerLinear_comp_ucp (c : Y → ℕ) (B : A →ₗ[ℂ] Matrix Y Y ℂ) (hone : B 1 = 1)
    (hcp : IsCompletelyPositiveOnMatrices Y ⇑B) :
    (layerLinear c ∘ₗ B) 1 = 1 ∧
      IsCompletelyPositiveOnMatrices (layerModel Y c) ⇑(layerLinear c ∘ₗ B) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.comp_apply, hone, layerLinear_apply, layer_one]
  · have h := isCompletelyPositiveOnMatrices_sum_conj Y (layerModel Y c) (⇑B) hcp
      (fun k : Fin (∑ i, c i) ↦ layerVec c (k : ℕ))
    have e : ⇑(layerLinear c ∘ₗ B) = fun x ↦
        ∑ k : Fin (∑ i, c i), (layerVec c (k : ℕ))ᴴ * B x * layerVec c (k : ℕ) := by
      funext x
      rw [LinearMap.comp_apply, layerLinear_apply, layer_eq_sum_conj]
    first
      | (rw [e]; exact h)
      | exact e ▸ h

end

end GroupApproximation.Full.TWWSchafhauser.Connes
