/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Statement
import GroupApproximation.BHPalomar.GraphProducts.FreeProductMap
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# The retract amalgam as a semidirect product

Let `r : X → C` be a retraction onto `ι : C → X` (so `r ∘ ι = id`), and `L = ker r`. The
amalgam `G = X *_C (C × K)` maps to `N ⋊ C`, where `N = K ∗ L` and `C` acts trivially on `K`
and by conjugation on `L`. That map has a left inverse (`lam_psi`), so it is injective
(`psi_injective`). This is Step 5 of the route: `G = (K ∗ L) ⋊ C`, proved by universal
properties alone.

The two free factors are realized as subgroups of `X × K`: `factorT D true = L × 1` and
`factorT D false = 1 × K`. Then `C` acts on both by conjugation with `(ι c, 1)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid

/-- The data of the retract-amalgam embedding: a retraction `r` of `ι`, and embeddings `φ` of
`X` and `ψ` of `K` into one group `H` in which `φ (ι C)` commutes with `ψ K`. -/
structure RetractData (X C K H : Type) [Group X] [Group C] [Group K] [Group H] where
  ι : C →* X
  r : X →* C
  hr : ∀ c, r (ι c) = c
  φ : X →* H
  hφ : Function.Injective φ
  ψ : K →* H
  hψ : Function.Injective ψ
  comm : ∀ c k, φ (ι c) * ψ k = ψ k * φ (ι c)

variable {X C K H : Type} [Group X] [Group C] [Group K] [Group H] (D : RetractData X C K H)

/-- The two free factors of `N`: `L × 1` (`true`) and `1 × K` (`false`), inside `X × K`. -/
def factorT (b : Bool) : Subgroup (X × K) :=
  bif b then D.r.ker.prod ⊥ else (⊥ : Subgroup X).prod ⊤

theorem mem_factorT_true {p : X × K} : p ∈ factorT D true ↔ D.r p.1 = 1 ∧ p.2 = 1 := by
  simp [factorT, Subgroup.mem_prod]

theorem mem_factorT_false {p : X × K} : p ∈ factorT D false ↔ p.1 = 1 := by
  simp [factorT, Subgroup.mem_prod]

/-- `N = K ∗ L`. -/
abbrev NN := Monoid.CoprodI fun b : Bool => ↥(factorT D b)

theorem conj_mem_factorT (c : C) (b : Bool) {p : X × K} (hp : p ∈ factorT D b) :
    MonoidHom.inl X K (D.ι c) * p * (MonoidHom.inl X K (D.ι c))⁻¹ ∈ factorT D b := by
  cases b
  · rw [mem_factorT_false] at hp ⊢
    simp [hp]
  · rw [mem_factorT_true] at hp ⊢
    simp [hp, D.hr]

/-- Conjugation by `(ι c, 1)` on a factor. -/
def conjT (c : C) (b : Bool) : ↥(factorT D b) →* ↥(factorT D b) where
  toFun t := ⟨MonoidHom.inl X K (D.ι c) * t * (MonoidHom.inl X K (D.ι c))⁻¹,
    conj_mem_factorT D c b t.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show MonoidHom.inl X K (D.ι c) * ((s : X × K) * t) * (MonoidHom.inl X K (D.ι c))⁻¹ =
      (MonoidHom.inl X K (D.ι c) * s * (MonoidHom.inl X K (D.ι c))⁻¹) *
        (MonoidHom.inl X K (D.ι c) * t * (MonoidHom.inl X K (D.ι c))⁻¹)
    group)

theorem conjT_coe (c : C) (b : Bool) (t : ↥(factorT D b)) :
    ((conjT D c b t : ↥(factorT D b)) : X × K) =
      MonoidHom.inl X K (D.ι c) * t * (MonoidHom.inl X K (D.ι c))⁻¹ :=
  rfl

theorem conjT_fst (c : C) (b : Bool) (t : ↥(factorT D b)) :
    ((conjT D c b t : ↥(factorT D b)) : X × K).1 = D.ι c * (t : X × K).1 * (D.ι c)⁻¹ := by
  simp [conjT_coe]

theorem conjT_snd (c : C) (b : Bool) (t : ↥(factorT D b)) :
    ((conjT D c b t : ↥(factorT D b)) : X × K).2 = (t : X × K).2 := by
  simp [conjT_coe]

/-- The action of `c` on `N`. -/
def actEnd (c : C) : NN D →* NN D :=
  Monoid.CoprodI.lift fun b => (Monoid.CoprodI.of (i := b)).comp (conjT D c b)

@[simp] theorem actEnd_of (c : C) (b : Bool) (t : ↥(factorT D b)) :
    actEnd D c (Monoid.CoprodI.of (i := b) t) = Monoid.CoprodI.of (conjT D c b t) := by
  simp [actEnd]

theorem actEnd_mul (c d : C) : actEnd D (c * d) = (actEnd D c).comp (actEnd D d) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext t
  simp only [MonoidHom.comp_apply, actEnd_of]
  congr 1
  apply Subtype.ext
  simp only [conjT_coe, map_mul]
  group

theorem actEnd_one : actEnd D 1 = MonoidHom.id (NN D) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext t
  simp only [MonoidHom.comp_apply, actEnd_of, MonoidHom.id_apply]
  congr 1
  apply Subtype.ext
  simp [conjT_coe]

/-- `C` acting on `N = K ∗ L`. -/
def act : C →* MulAut (NN D) := autOfEnd (actEnd D) (actEnd_mul D) (actEnd_one D)

@[simp] theorem act_of (c : C) (b : Bool) (t : ↥(factorT D b)) :
    act D c (Monoid.CoprodI.of (i := b) t) = Monoid.CoprodI.of (conjT D c b t) := by
  simp [act]

/-- `S = (K ∗ L) ⋊ C`. -/
abbrev SS := NN D ⋊[act D] C

/-! ### The map `G → S` -/

/-- `x ι(r x)⁻¹ ∈ L`. -/
def elemT (x : X) : ↥(factorT D true) :=
  ⟨(x * D.ι (D.r x)⁻¹, 1), (mem_factorT_true D).mpr ⟨by simp [D.hr], rfl⟩⟩

theorem elemT_coe (x : X) : ((elemT D x : ↥(factorT D true)) : X × K) = (x * D.ι (D.r x)⁻¹, 1) :=
  rfl

/-- `k ∈ K`. -/
def elemF (k : K) : ↥(factorT D false) :=
  ⟨(1, k), (mem_factorT_false D).mpr rfl⟩

theorem elemF_coe (k : K) : ((elemF D k : ↥(factorT D false)) : X × K) = (1, k) :=
  rfl

/-- `x ↦ (x ι(r x)⁻¹, r x)`. -/
def psiX : X →* SS D :=
  MonoidHom.mk' (fun x => ⟨Monoid.CoprodI.of (elemT D x), D.r x⟩) (fun x y => by
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left]
      rw [act_of, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, conjT_coe, elemT_coe]
      ext
      · simp only [Prod.fst_mul, Prod.fst_inv, MonoidHom.inl_apply, map_mul, map_inv]
        group
      · simp
    · simp only [SemidirectProduct.mul_right, map_mul])

theorem psiX_apply (x : X) : psiX D x = ⟨Monoid.CoprodI.of (elemT D x), D.r x⟩ := rfl

/-- `(c, k) ↦ (k, c)`. -/
def psiCK : C × K →* SS D :=
  MonoidHom.mk' (fun p => ⟨Monoid.CoprodI.of (elemF D p.2), p.1⟩) (fun p q => by
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left]
      rw [act_of, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, conjT_coe, elemF_coe]
      ext
      · simp
      · simp
    · simp only [SemidirectProduct.mul_right, Prod.fst_mul])

theorem psiCK_apply (p : C × K) : psiCK D p = ⟨Monoid.CoprodI.of (elemF D p.2), p.1⟩ := rfl

theorem psi_rel (c : C) : psiX D (D.ι c) = psiCK D (c, 1) := by
  apply SemidirectProduct.ext
  · show Monoid.CoprodI.of (elemT D (D.ι c)) = Monoid.CoprodI.of (elemF D (1 : K))
    have h1 : elemT D (D.ι c) = 1 := Subtype.ext (by simp [elemT_coe, D.hr])
    have h2 : elemF D (1 : K) = 1 := Subtype.ext (by simp [elemF_coe])
    rw [h1, h2, map_one, map_one]
  · exact D.hr c

/-- `Ψ : X *_C (C × K) → (K ∗ L) ⋊ C`. -/
def Psi : RetractAmalgam D.ι K →* SS D :=
  QuotientGroup.lift _ (Coprod.lift (psiX D) (psiCK D)) (Subgroup.normalClosure_le_normal (by
    simp only [retractAmalgamRels, Set.range_subset_iff]
    intro c
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, Coprod.lift_apply_inl,
      Coprod.lift_apply_inr, psi_rel, mul_inv_cancel]))

theorem Psi_mk (y : Coprod X (C × K)) :
    Psi D (QuotientGroup.mk' _ y) = Coprod.lift (psiX D) (psiCK D) y :=
  QuotientGroup.lift_mk' _ _

/-! ### The inverse map `S → G` -/

theorem amalg_rel (c : C) :
    (QuotientGroup.mk' _ (Coprod.inl (D.ι c)) : RetractAmalgam D.ι K) =
      QuotientGroup.mk' _ (Coprod.inr (c, (1 : K))) := by
  have h1 : (QuotientGroup.mk' (Subgroup.normalClosure (retractAmalgamRels D.ι K))
      (Coprod.inl (D.ι c) * (Coprod.inr (c, (1 : K)))⁻¹)) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure ⟨c, rfl⟩
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

/-- The factors of `N` back into `G`. -/
def lamT : ∀ b : Bool, ↥(factorT D b) →* RetractAmalgam D.ι K
  | true => (QuotientGroup.mk' _).comp
      (Coprod.inl.comp ((MonoidHom.fst X K).comp (factorT D true).subtype))
  | false => (QuotientGroup.mk' _).comp
      (Coprod.inr.comp ((MonoidHom.inr C K).comp ((MonoidHom.snd X K).comp (factorT D false).subtype)))

theorem lamT_true_apply (s : ↥(factorT D true)) :
    lamT D true s = QuotientGroup.mk' _ (Coprod.inl (s : X × K).1) := rfl

theorem lamT_false_apply (s : ↥(factorT D false)) :
    lamT D false s = QuotientGroup.mk' _ (Coprod.inr ((1 : C), (s : X × K).2)) := rfl

/-- `C` into `G`. -/
def lamC : C →* RetractAmalgam D.ι K :=
  (QuotientGroup.mk' _).comp (Coprod.inr.comp (MonoidHom.inl C K))

theorem lamC_apply (c : C) : lamC D c = QuotientGroup.mk' _ (Coprod.inr (c, (1 : K))) := rfl

/-- `N` into `G`. -/
def lamN : NN D →* RetractAmalgam D.ι K := Monoid.CoprodI.lift (lamT D)

@[simp] theorem lamN_of (b : Bool) (t : ↥(factorT D b)) :
    lamN D (Monoid.CoprodI.of (i := b) t) = lamT D b t :=
  Monoid.CoprodI.lift_of _ _

theorem lamT_conj_true (c : C) (t : ↥(factorT D true)) :
    lamT D true (conjT D c true t) = lamC D c * lamT D true t * (lamC D c)⁻¹ := by
  rw [lamT_true_apply, lamT_true_apply, lamC_apply, ← amalg_rel, conjT_coe]
  simp only [Prod.fst_mul, Prod.fst_inv, MonoidHom.inl_apply, map_mul, map_inv]

theorem lamT_conj_false (c : C) (t : ↥(factorT D false)) :
    lamT D false (conjT D c false t) = lamC D c * lamT D false t * (lamC D c)⁻¹ := by
  rw [lamT_false_apply, lamT_false_apply, lamC_apply, conjT_snd]
  have e : (Coprod.inr (c, (1 : K)) * Coprod.inr ((1 : C), (t : X × K).2) *
      (Coprod.inr (c, (1 : K)))⁻¹ : Coprod X (C × K)) = Coprod.inr ((1 : C), (t : X × K).2) := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    ext <;> simp
  conv_lhs => rw [← e]
  rw [map_mul, map_mul, map_inv]

theorem lam_compat (c : C) :
    (lamN D).comp (act D c).toMonoidHom = (MulAut.conj (lamC D c)).toMonoidHom.comp (lamN D) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  ext t
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, act_of, lamN_of, MulAut.conj_apply]
  cases b
  · exact lamT_conj_false D c t
  · exact lamT_conj_true D c t

/-- `Λ : (K ∗ L) ⋊ C → G`. -/
def Lam : SS D →* RetractAmalgam D.ι K := SemidirectProduct.lift (lamN D) (lamC D) (lam_compat D)

theorem Lam_mk (n : NN D) (c : C) : Lam D ⟨n, c⟩ = lamN D n * lamC D c := rfl

theorem lam_psi : (Lam D).comp (Psi D) = MonoidHom.id _ := by
  apply QuotientGroup.monoidHom_ext
  apply Coprod.hom_ext
  · ext x
    show Lam D (Psi D (QuotientGroup.mk' _ (Coprod.inl x))) = QuotientGroup.mk' _ (Coprod.inl x)
    rw [Psi_mk, Coprod.lift_apply_inl, psiX_apply, Lam_mk, lamN_of, lamT_true_apply, elemT_coe,
      lamC_apply, ← amalg_rel, ← map_mul, ← map_mul]
    congr 2
    simp [map_inv]
  · ext p
    show Lam D (Psi D (QuotientGroup.mk' _ (Coprod.inr p))) = QuotientGroup.mk' _ (Coprod.inr p)
    rw [Psi_mk, Coprod.lift_apply_inr, psiCK_apply, Lam_mk, lamN_of, lamT_false_apply, elemF_coe,
      lamC_apply, ← map_mul, ← map_mul]
    congr 2
    ext <;> simp

/-- **Step 5a**: `X *_C (C × K) → (K ∗ L) ⋊ C` is injective. -/
theorem psi_injective : Function.Injective (Psi D) :=
  Function.LeftInverse.injective (g := Lam D) fun a => DFunLike.congr_fun (lam_psi D) a

end GroupApproximation.BHPalomar.GraphProducts
