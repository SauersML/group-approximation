import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalCompose
import Mathlib.RingTheory.Ideal.Maximal
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 3: the Quillen ideal of a normalized matrix

Lane `bh-met-53`.  For `τ ∈ GL_N(A[X])` put

  `Q(τ) = {a ∈ A : τ(X + aY) τ(X)⁻¹ ∈ E_N(A[X][Y])}`.

This is an ideal (`suslinLocalGlobalQuillenIdeal`):

* `0 ∈ Q(τ)`, since `τ(X + 0Y) τ(X)⁻¹ = 1`;
* `a ∈ Q(τ) ⇒ ca ∈ Q(τ)`: apply the substitution `Y ↦ cY`, which maps `E_N` into `E_N`;
* `a, b ∈ Q(τ) ⇒ a + b ∈ Q(τ)`: apply `X ↦ X + bY` to `τ(X + aY) τ(X)⁻¹`, giving
  `τ(X + (a + b)Y) τ(X + bY)⁻¹`, and multiply by `τ(X + bY) τ(X)⁻¹`.

**Quillen patching for `E_N`** (`suslinLocalGlobal_mem_elementaryGroup`): if `τ(0) = 1` and
`Q(τ)` is contained in no maximal ideal, then `Q(τ) = A`, so `τ(X + Y) τ(X)⁻¹` is elementary,
and the substitution `X ↦ 0, Y ↦ X` turns it into `τ(X) τ(0)⁻¹ = τ(X)`.  No rank bound, no
determinant condition and no Noetherian hypothesis is used.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A] {N : ℕ}

/-- `a ∈ Q(τ)`: the matrix `τ(X + aY) τ(X)⁻¹` over `A[X][Y]` is elementary. -/
def SuslinLocalGlobalQuillen (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) (a : A) :
    Prop :=
  elementaryMatrixUnitMap (ι := Fin N) (suslinLocalGlobalShift a) τ *
      (elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) τ)⁻¹ ∈
    elementaryGroup (Fin N) (Polynomial (Polynomial A))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinLocalGlobalQuillen

theorem suslinLocalGlobalQuillen_zero (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
    SuslinLocalGlobalQuillen τ (0 : A) := by
  unfold SuslinLocalGlobalQuillen
  rw [suslinLocalGlobalShift_zero, mul_inv_cancel]
  exact one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalQuillen_zero

theorem suslinLocalGlobalQuillen_mul (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (c : A) {a : A} (ha : SuslinLocalGlobalQuillen τ a) :
    SuslinLocalGlobalQuillen τ (c * a) := by
  unfold SuslinLocalGlobalQuillen at ha ⊢
  have hmem := elementaryGroup_map_le (ι := Fin N) (suslinLocalGlobalDilate c)
    (Subgroup.mem_map_of_mem _ ha)
  rwa [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
    suslinLocalGlobalDilate_comp_shift, suslinLocalGlobalDilate_comp_C] at hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalQuillen_mul

theorem suslinLocalGlobalQuillen_add (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    {a b : A} (ha : SuslinLocalGlobalQuillen τ a) (hb : SuslinLocalGlobalQuillen τ b) :
    SuslinLocalGlobalQuillen τ (a + b) := by
  unfold SuslinLocalGlobalQuillen at ha hb ⊢
  have hmem := elementaryGroup_map_le (ι := Fin N) (suslinLocalGlobalTranslate b)
    (Subgroup.mem_map_of_mem _ ha)
  rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
    suslinLocalGlobalTranslate_comp_shift, suslinLocalGlobalTranslate_comp_C] at hmem
  have hprod := mul_mem hmem hb
  rwa [mul_assoc, inv_mul_cancel_left] at hprod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalQuillen_add

/-- **The Quillen ideal** `Q(τ)` of `τ ∈ GL_N(A[X])`. -/
noncomputable def suslinLocalGlobalQuillenIdeal
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) : Ideal A where
  carrier := {a | SuslinLocalGlobalQuillen τ a}
  add_mem' := fun {a b} ha hb ↦ suslinLocalGlobalQuillen_add τ (a := a) (b := b) ha hb
  zero_mem' := suslinLocalGlobalQuillen_zero τ
  smul_mem' := fun c {x} hx ↦ suslinLocalGlobalQuillen_mul τ c (a := x) hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalQuillenIdeal

/-- **Quillen patching for the elementary group.**  If `τ ∈ GL_N(A[X])` satisfies `τ(0) = 1`
and for every maximal ideal `𝔪` some `a ∉ 𝔪` has `τ(X + aY) τ(X)⁻¹ ∈ E_N(A[X][Y])`, then
`τ ∈ E_N(A[X])`. -/
theorem suslinLocalGlobal_mem_elementaryGroup
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hτ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1)
    (hloc : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ a ∉ 𝔪, SuslinLocalGlobalQuillen τ a) :
    τ ∈ elementaryGroup (Fin N) (Polynomial A) := by
  have htop : suslinLocalGlobalQuillenIdeal τ = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨a, ha𝔪, ha⟩ := hloc 𝔪 h𝔪
    exact ha𝔪 (hle (show a ∈ suslinLocalGlobalQuillenIdeal τ from ha))
  have h1' : (1 : A) ∈ suslinLocalGlobalQuillenIdeal τ := (Ideal.eq_top_iff_one _).1 htop
  have h1 : SuslinLocalGlobalQuillen τ (1 : A) := h1'
  unfold SuslinLocalGlobalQuillen at h1
  have hmem := elementaryGroup_map_le (ι := Fin N) (suslinLocalGlobalRestrict (A := A))
    (Subgroup.mem_map_of_mem _ h1)
  rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinLocalGlobal_map_map,
    suslinLocalGlobalRestrict_comp_shift_one, suslinLocalGlobalRestrict_comp_C,
    suslinLocalGlobal_map_id, ← suslinLocalGlobal_map_map, hτ0, map_one, inv_one,
    mul_one] at hmem
  exact hmem

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobal_mem_elementaryGroup

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
