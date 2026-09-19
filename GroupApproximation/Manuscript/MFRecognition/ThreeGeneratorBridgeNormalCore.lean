import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgeQuotient

/-!
# The three-generator bridge, part 4: `N_0 = F(y_n) × F(t_m)`

This file formalizes the middle of the printed proof of `lem:bridge` (3):

> Let `N_0` be the normal closure of `{y,t}` in `Q_+`.  Then `Q_+/N_0 = ⟨x⟩` is
> infinite cyclic and the extension splits, so `Q_+ = N_0 ⋊ ⟨x⟩`.  Rewriting the
> presentation of `Q_+` over the transversal `{x^n}` by the
> Reidemeister--Schreier method presents `N_0` on the generators
> `y_n = x^n y x^{-n}` and `t_m = x^m t x^{-m}`, `n,m ∈ ℤ`, with relators the
> conjugates `x^m [t,y_n] x^{-m} = [t_m, y_{n+m}]`, that is, all commutators
> `[t_m, y_n]`.  So `N_0 = F(y_n : n ∈ ℤ) × F(t_m : m ∈ ℤ)`.

The manuscript reaches the identification by Reidemeister--Schreier
(Lyndon--Schupp, Chapter II).  It is verified directly here instead, so no
literature input is consumed: the commutators `[t_m, y_n] = 1` are read off the
defining relation of `B(1)` (`qplus_commute`), which gives a homomorphism

  `Theta : F(ℤ) × F(ℤ) → Q_+`,  `(a,b) ↦ y(a) · t(b)`,

whose range is exactly `N_0` (`nzeroModel_eq_Nzero`); its *injectivity* --- the
remaining half of the printed identification --- is proved in
`ThreeGeneratorBridgeInjective`, where it falls out of `j` itself.

The printed splitting `Q_+ = N_0 ⋊ ⟨x⟩` appears as `exists_split`: every
element of `Q_+` is `h · x^k` with `h ∈ N_0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge

open GroupApproximation.Higman.HNNEmb
open GroupApproximation.Higman

/-! ## 1.  The printed families `y_n` and `t_m` inside `Q_+` -/

/-- `y_n = x^n y x^{-n}`, in `Q_+`. -/
noncomputable def qyFam (n : ℤ) : Qplus := qx ^ n * qy * qx ^ (-n)

/-- `t_m = x^m t x^{-m}`, in `Q_+`. -/
noncomputable def qtFam (m : ℤ) : Qplus := qx ^ m * qt * qx ^ (-m)

theorem qyFam_zero : qyFam 0 = qy := by
  show qx ^ (0 : ℤ) * qy * qx ^ (-(0 : ℤ)) = qy
  rw [neg_zero, zpow_zero, one_mul, mul_one]

theorem qtFam_zero : qtFam 0 = qt := by
  show qx ^ (0 : ℤ) * qt * qx ^ (-(0 : ℤ)) = qt
  rw [neg_zero, zpow_zero, one_mul, mul_one]

theorem qyFam_eq (n : ℤ) : qyFam n = HNNExtension.of (yBase Triv n) := by
  show qx ^ n * qy * qx ^ (-n)
    = HNNExtension.of ((xg : Higman.HNNEmb.P Triv) ^ n * yg * (xg : Higman.HNNEmb.P Triv) ^ (-n))
  rw [map_mul, map_mul, map_zpow, map_zpow, qx_eq, qy_eq]

/-- **The printed relators `[t, y_n] = 1` of `Q_+`.** -/
theorem qt_commute_qyFam (n : ℤ) : Commute qt (qyFam n) := by
  have h := qplus_commute (FreeGroup.of n)
  rw [yBaseHom_of] at h
  show qt * qyFam n = qyFam n * qt
  rw [qt_eq, qyFam_eq]
  exact h

theorem qx_conj_qyFam (d n : ℤ) : qx ^ d * qyFam n * qx ^ (-d) = qyFam (n + d) := by
  have h1 : qx ^ (n + d) = qx ^ d * qx ^ n := by
    rw [← zpow_add]
    congr 1
    ring
  have h2 : qx ^ (-(n + d)) = qx ^ (-n) * qx ^ (-d) := by
    rw [← zpow_add]
    congr 1
    ring
  show qx ^ d * (qx ^ n * qy * qx ^ (-n)) * qx ^ (-d)
    = qx ^ (n + d) * qy * qx ^ (-(n + d))
  rw [h1, h2]
  simp only [mul_assoc]

theorem qx_conj_qtFam (d m : ℤ) : qx ^ d * qtFam m * qx ^ (-d) = qtFam (m + d) := by
  have h1 : qx ^ (m + d) = qx ^ d * qx ^ m := by
    rw [← zpow_add]
    congr 1
    ring
  have h2 : qx ^ (-(m + d)) = qx ^ (-m) * qx ^ (-d) := by
    rw [← zpow_add]
    congr 1
    ring
  show qx ^ d * (qx ^ m * qt * qx ^ (-m)) * qx ^ (-d)
    = qx ^ (m + d) * qt * qx ^ (-(m + d))
  rw [h1, h2]
  simp only [mul_assoc]

theorem qyFam_conj (m n : ℤ) : qx ^ m * qyFam (n - m) * qx ^ (-m) = qyFam n := by
  have h := qx_conj_qyFam m (n - m)
  rw [h]
  congr 1
  ring

/-- **The printed relators `[t_m, y_n] = 1`**: the conjugates
`x^m [t, y_n] x^{-m} = [t_m, y_{n+m}]` exhaust all commutators of the two
families. -/
theorem qtFam_commute_qyFam (m n : ℤ) : Commute (qtFam m) (qyFam n) := by
  have hy := qyFam_conj m n
  have hc := (qt_commute_qyFam (n - m)).eq
  have hcancel : qx ^ (-m) * qx ^ m = 1 := by
    rw [← zpow_add, neg_add_cancel, zpow_zero]
  show qtFam m * qyFam n = qyFam n * qtFam m
  rw [← hy]
  show (qx ^ m * qt * qx ^ (-m)) * (qx ^ m * qyFam (n - m) * qx ^ (-m))
    = (qx ^ m * qyFam (n - m) * qx ^ (-m)) * (qx ^ m * qt * qx ^ (-m))
  calc (qx ^ m * qt * qx ^ (-m)) * (qx ^ m * qyFam (n - m) * qx ^ (-m))
      = qx ^ m * (qt * (qx ^ (-m) * qx ^ m) * qyFam (n - m)) * qx ^ (-m) := by
        simp only [mul_assoc]
    _ = qx ^ m * (qt * qyFam (n - m)) * qx ^ (-m) := by
        rw [hcancel, mul_one]
    _ = qx ^ m * (qyFam (n - m) * qt) * qx ^ (-m) := by rw [hc]
    _ = qx ^ m * (qyFam (n - m) * (qx ^ (-m) * qx ^ m) * qt) * qx ^ (-m) := by
        rw [hcancel, mul_one]
    _ = (qx ^ m * qyFam (n - m) * qx ^ (-m)) * (qx ^ m * qt * qx ^ (-m)) := by
        simp only [mul_assoc]

/-! ## 2.  The two free factors -/

/-- `F(y_n : n ∈ ℤ) → Q_+`. -/
noncomputable def qyHom : FreeGroup ℤ →* Qplus := FreeGroup.lift qyFam

/-- `F(t_m : m ∈ ℤ) → Q_+`. -/
noncomputable def qtHom : FreeGroup ℤ →* Qplus := FreeGroup.lift qtFam

theorem qyHom_of (n : ℤ) : qyHom (FreeGroup.of n) = qyFam n := by
  simp [qyHom]

theorem qtHom_of (m : ℤ) : qtHom (FreeGroup.of m) = qtFam m := by
  simp [qtHom]

theorem commute_qtFam_qyHom (m : ℤ) (a : FreeGroup ℤ) :
    Commute (qtFam m) (qyHom a) := by
  refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Commute.one_right _
  · intro n
    rw [qyHom_of]
    exact qtFam_commute_qyFam m n
  · intro n h
    rw [map_inv]
    exact h.inv_right
  · intro u v hu hv
    rw [map_mul]
    exact hu.mul_right hv

theorem commute_qtHom_qyHom (b a : FreeGroup ℤ) : Commute (qtHom b) (qyHom a) := by
  refine FreeGroup.induction_on b ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Commute.one_left _
  · intro m
    rw [qtHom_of]
    exact commute_qtFam_qyHom m a
  · intro m h
    rw [map_inv]
    exact h.inv_left
  · intro u v hu hv
    rw [map_mul]
    exact hu.mul_left hv

/-- **The printed direct product `F(y_n) × F(t_m)`, mapped into `Q_+`.** -/
noncomputable def Theta : FreeGroup ℤ × FreeGroup ℤ →* Qplus :=
  MonoidHom.mk' (fun p => qyHom p.1 * qtHom p.2) (fun p q => by
    show qyHom (p.1 * q.1) * qtHom (p.2 * q.2)
      = (qyHom p.1 * qtHom p.2) * (qyHom q.1 * qtHom q.2)
    rw [map_mul, map_mul]
    have h := (commute_qtHom_qyHom p.2 q.1).eq
    calc qyHom p.1 * qyHom q.1 * (qtHom p.2 * qtHom q.2)
        = qyHom p.1 * (qyHom q.1 * qtHom p.2) * qtHom q.2 := by simp only [mul_assoc]
      _ = qyHom p.1 * (qtHom p.2 * qyHom q.1) * qtHom q.2 := by rw [← h]
      _ = qyHom p.1 * qtHom p.2 * (qyHom q.1 * qtHom q.2) := by simp only [mul_assoc])

theorem Theta_apply (a b : FreeGroup ℤ) : Theta (a, b) = qyHom a * qtHom b := rfl

/-- The image of the printed direct product. -/
noncomputable def NzeroModel : Subgroup Qplus := Theta.range

theorem qy_mem_model : qy ∈ NzeroModel := by
  refine ⟨(FreeGroup.of 0, 1), ?_⟩
  rw [Theta_apply, qyHom_of, qyFam_zero, map_one, mul_one]

theorem qt_mem_model : qt ∈ NzeroModel := by
  refine ⟨(1, FreeGroup.of 0), ?_⟩
  rw [Theta_apply, qtHom_of, qtFam_zero, map_one, one_mul]

/-! ## 3.  `N_0` and the identification -/

/-- **`N_0`**, the normal closure of `{y, t}` in `Q_+`. -/
noncomputable def Nzero : Subgroup Qplus :=
  Subgroup.normalClosure ({qy, qt} : Set Qplus)

theorem nzero_normal : Nzero.Normal := Subgroup.normalClosure_normal

theorem qy_mem_Nzero : qy ∈ Nzero :=
  Subgroup.subset_normalClosure (Set.mem_insert _ _)

theorem qt_mem_Nzero : qt ∈ Nzero :=
  Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)

theorem qyFam_mem_Nzero (n : ℤ) : qyFam n ∈ Nzero := by
  have h := nzero_normal.conj_mem qy qy_mem_Nzero (qx ^ n)
  show qx ^ n * qy * qx ^ (-n) ∈ Nzero
  rwa [← zpow_neg] at h

theorem qtFam_mem_Nzero (m : ℤ) : qtFam m ∈ Nzero := by
  have h := nzero_normal.conj_mem qt qt_mem_Nzero (qx ^ m)
  show qx ^ m * qt * qx ^ (-m) ∈ Nzero
  rwa [← zpow_neg] at h

theorem qyHom_mem_Nzero (a : FreeGroup ℤ) : qyHom a ∈ Nzero := by
  refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro n
    rw [qyHom_of]
    exact qyFam_mem_Nzero n
  · intro n h
    rw [map_inv]
    exact Subgroup.inv_mem _ h
  · intro u v hu hv
    rw [map_mul]
    exact Subgroup.mul_mem _ hu hv

theorem qtHom_mem_Nzero (b : FreeGroup ℤ) : qtHom b ∈ Nzero := by
  refine FreeGroup.induction_on b ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro m
    rw [qtHom_of]
    exact qtFam_mem_Nzero m
  · intro m h
    rw [map_inv]
    exact Subgroup.inv_mem _ h
  · intro u v hu hv
    rw [map_mul]
    exact Subgroup.mul_mem _ hu hv

theorem model_le_Nzero : NzeroModel ≤ Nzero := by
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [Theta_apply]
  exact Subgroup.mul_mem _ (qyHom_mem_Nzero a) (qtHom_mem_Nzero b)

/-! ## 4.  The image of `Theta` is normal -/

/-- Shifting the printed index of the free generators. -/
def shift (d : ℤ) : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun n => FreeGroup.of (n + d))

theorem shift_of (d n : ℤ) : shift d (FreeGroup.of n) = FreeGroup.of (n + d) := by
  simp [shift]

/-- Conjugation by a fixed element, as an endomorphism. -/
def conjHom {G : Type*} [Group G] (g : G) : G →* G where
  toFun u := g * u * g⁻¹
  map_one' := by
    show g * 1 * g⁻¹ = 1
    rw [mul_one, mul_inv_cancel]
  map_mul' u v := by
    show g * (u * v) * g⁻¹ = g * u * g⁻¹ * (g * v * g⁻¹)
    group

theorem conjHom_comp_qyHom (d : ℤ) :
    (conjHom (qx ^ d)).comp qyHom = qyHom.comp (shift d) := by
  refine FreeGroup.ext_hom _ _ fun n => ?_
  show qx ^ d * qyHom (FreeGroup.of n) * (qx ^ d)⁻¹
    = qyHom (shift d (FreeGroup.of n))
  rw [qyHom_of, shift_of, qyHom_of, ← zpow_neg]
  exact qx_conj_qyFam d n

theorem conjHom_comp_qtHom (d : ℤ) :
    (conjHom (qx ^ d)).comp qtHom = qtHom.comp (shift d) := by
  refine FreeGroup.ext_hom _ _ fun m => ?_
  show qx ^ d * qtHom (FreeGroup.of m) * (qx ^ d)⁻¹
    = qtHom (shift d (FreeGroup.of m))
  rw [qtHom_of, shift_of, qtHom_of, ← zpow_neg]
  exact qx_conj_qtFam d m

theorem conj_qx_qyHom (d : ℤ) (a : FreeGroup ℤ) :
    qx ^ d * qyHom a * (qx ^ d)⁻¹ = qyHom (shift d a) :=
  congrArg (fun f : FreeGroup ℤ →* Qplus => f a) (conjHom_comp_qyHom d)

theorem conj_qx_qtHom (d : ℤ) (b : FreeGroup ℤ) :
    qx ^ d * qtHom b * (qx ^ d)⁻¹ = qtHom (shift d b) :=
  congrArg (fun f : FreeGroup ℤ →* Qplus => f b) (conjHom_comp_qtHom d)

theorem conj_mul_distrib (g u v : Qplus) :
    g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group

theorem conj_mul_left (z w v : Qplus) :
    z * w * v * (z * w)⁻¹ = z * (w * v * w⁻¹) * z⁻¹ := by group

theorem conj_mul_left_inv (z w v : Qplus) :
    (z * w)⁻¹ * v * (z * w) = w⁻¹ * (z⁻¹ * v * z) * w := by group

theorem conj_zpow_mem_model (d : ℤ) (v : Qplus) (hv : v ∈ NzeroModel) :
    qx ^ d * v * (qx ^ d)⁻¹ ∈ NzeroModel := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hv
  refine ⟨(shift d a, shift d b), ?_⟩
  rw [Theta_apply, Theta_apply, conj_mul_distrib, conj_qx_qyHom, conj_qx_qtHom]

theorem qx_conj_mem_model (v : Qplus) (hv : v ∈ NzeroModel) :
    qx * v * qx⁻¹ ∈ NzeroModel := by
  have h := conj_zpow_mem_model 1 v hv
  rwa [zpow_one] at h

theorem qxInv_conj_mem_model (v : Qplus) (hv : v ∈ NzeroModel) :
    qx⁻¹ * v * qx ∈ NzeroModel := by
  have h := conj_zpow_mem_model (-1) v hv
  rw [zpow_neg, zpow_one, inv_inv] at h
  exact h

theorem nzeroModel_conj_pair (g : Qplus) :
    (∀ v ∈ NzeroModel, g * v * g⁻¹ ∈ NzeroModel) ∧
      (∀ v ∈ NzeroModel, g⁻¹ * v * g ∈ NzeroModel) := by
  have hg : g ∈ Subgroup.closure ({qx, qy, qt} : Set Qplus) := by
    rw [closure_qgens]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction
    (p := fun z _ => (∀ v ∈ NzeroModel, z * v * z⁻¹ ∈ NzeroModel) ∧
      (∀ v ∈ NzeroModel, z⁻¹ * v * z ∈ NzeroModel)) ?_ ?_ ?_ ?_ hg
  · rintro z (rfl | rfl | rfl)
    · exact ⟨qx_conj_mem_model, qxInv_conj_mem_model⟩
    · exact ⟨fun v hv => Subgroup.mul_mem _
          (Subgroup.mul_mem _ qy_mem_model hv) (Subgroup.inv_mem _ qy_mem_model),
        fun v hv => Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ qy_mem_model) hv) qy_mem_model⟩
    · exact ⟨fun v hv => Subgroup.mul_mem _
          (Subgroup.mul_mem _ qt_mem_model hv) (Subgroup.inv_mem _ qt_mem_model),
        fun v hv => Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ qt_mem_model) hv) qt_mem_model⟩
  · refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [one_mul, inv_one, mul_one]
      exact hv
    · rw [inv_one, one_mul, mul_one]
      exact hv
  · intro z w _ _ hz hw
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [conj_mul_left]
      exact hz.1 _ (hw.1 v hv)
    · rw [conj_mul_left_inv]
      exact hw.2 _ (hz.2 v hv)
  · intro z _ hz
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [inv_inv]
      exact hz.2 v hv
    · rw [inv_inv]
      exact hz.1 v hv

theorem nzeroModel_normal : NzeroModel.Normal :=
  ⟨fun v hv g => (nzeroModel_conj_pair g).1 v hv⟩

theorem Nzero_le_model : Nzero ≤ NzeroModel := by
  haveI := nzeroModel_normal
  refine Subgroup.normalClosure_le_normal ?_
  rintro z (rfl | rfl)
  · exact qy_mem_model
  · exact qt_mem_model

/-- **`lem:bridge` (3), the Reidemeister--Schreier step, surjective half.**
"`N_0 = F(y_n : n ∈ ℤ) × F(t_m : m ∈ ℤ)`": the normal closure of `{y,t}` is
exactly the image of the direct product of the two free groups on the printed
families.  Injectivity of `Theta` --- the other half of the identification ---
is `Theta_injective`. -/
theorem nzeroModel_eq_Nzero : NzeroModel = Nzero :=
  le_antisymm model_le_Nzero Nzero_le_model

/-! ## 5.  The printed splitting `Q_+ = N_0 ⋊ ⟨x⟩` -/

/-- The set of printed normal forms `h · x^k`, `h ∈ N_0`. -/
noncomputable def SplitSub : Subgroup Qplus where
  carrier := {u : Qplus | ∃ h ∈ Nzero, ∃ k : ℤ, u = h * qx ^ k}
  one_mem' := ⟨1, Subgroup.one_mem _, 0, by rw [zpow_zero, mul_one]⟩
  mul_mem' := by
    rintro a b ⟨h₁, hh₁, k₁, rfl⟩ ⟨h₂, hh₂, k₂, rfl⟩
    refine ⟨h₁ * (qx ^ k₁ * h₂ * (qx ^ k₁)⁻¹),
      Subgroup.mul_mem _ hh₁ (nzero_normal.conj_mem h₂ hh₂ (qx ^ k₁)), k₁ + k₂, ?_⟩
    rw [zpow_add]
    group
  inv_mem' := by
    rintro a ⟨h, hh, k, rfl⟩
    refine ⟨(qx ^ k)⁻¹ * h⁻¹ * qx ^ k, ?_, -k, ?_⟩
    · have hc := nzero_normal.conj_mem h⁻¹ (Subgroup.inv_mem _ hh) ((qx ^ k)⁻¹)
      rwa [inv_inv] at hc
    · rw [zpow_neg]
      group

theorem splitSub_eq_top : SplitSub = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← closure_qgens, Subgroup.closure_le]
  rintro z (rfl | rfl | rfl)
  · exact ⟨1, Subgroup.one_mem _, 1, by rw [zpow_one, one_mul]⟩
  · exact ⟨qy, qy_mem_Nzero, 0, by rw [zpow_zero, mul_one]⟩
  · exact ⟨qt, qt_mem_Nzero, 0, by rw [zpow_zero, mul_one]⟩

/-- **`lem:bridge` (3), the printed splitting.**  "`Q_+/N_0 = ⟨x⟩` is infinite
cyclic and the extension splits, so `Q_+ = N_0 ⋊ ⟨x⟩`": every element of `Q_+`
is `h · x^k` with `h ∈ N_0`. -/
theorem exists_split (u : Qplus) : ∃ h ∈ Nzero, ∃ k : ℤ, u = h * qx ^ k := by
  have h : u ∈ SplitSub := by
    rw [splitSub_eq_top]
    exact Subgroup.mem_top u
  exact h

end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
