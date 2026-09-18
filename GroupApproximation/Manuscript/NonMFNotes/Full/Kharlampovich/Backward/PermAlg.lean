import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.KMSPresentation
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.OpsAlg

/-!
# The relations G3 and G4 for operators

Input for the "if" direction of KMS Theorem `tmm`(b) (`l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

Generic permutation facts behind G3 and G4:
* `g3a_of`: if `B = 1 + P`, `a` acts by a table `T` and `a'` by `T + id`, then
  `B^{a⁻¹} B⁻¹ = B^{(a')⁻¹}`;
* `g3b_of`: `[B^Z, B] = 1` for every `Z` in the subgroup `fixSub act` of additive
  permutations that are the identity on inactive classes.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {K : ℕ}

theorem perm_inv_apply_self {α : Type*} (Z : Equiv.Perm α) (x : α) : Z⁻¹ (Z x) = x :=
  Z.symm_apply_apply x

theorem perm_apply_inv_self {α : Type*} (Z : Equiv.Perm α) (x : α) : Z (Z⁻¹ x) = x :=
  Z.apply_symm_apply x

theorem khComm_eq_one_of_mul_comm {G : Type*} [Group G] {u v : G} (h : u * v = v * u) :
    khComm u v = 1 := by
  have e : khComm u v = u⁻¹ * (v⁻¹ * (u * v)) := by
    simp only [khComm, mul_assoc]
  rw [e, h, inv_mul_cancel_left, inv_mul_cancel]

/-- An additive permutation that is the identity at inactive classes. -/
structure IsFix {C : Type*} (act : C → Prop) (Z : Equiv.Perm (Fn K C)) : Prop where
  /-- Additivity. -/
  add : ∀ φ ψ, Z (φ + ψ) = Z φ + Z ψ
  /-- Identity at inactive classes. -/
  fix : ∀ φ v c, ¬ act c → Z φ v c = φ v c

theorem IsFix.one {C : Type*} (act : C → Prop) : IsFix act (1 : Equiv.Perm (Fn K C)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ _ ↦ rfl⟩

theorem IsFix.mul {C : Type*} {act : C → Prop} {Y Z : Equiv.Perm (Fn K C)}
    (hY : IsFix act Y) (hZ : IsFix act Z) : IsFix act (Y * Z) :=
  ⟨fun φ ψ ↦ (congrArg (fun p ↦ Y p) (hZ.add φ ψ)).trans (hY.add (Z φ) (Z ψ)),
    fun φ v c hc ↦ (hY.fix (Z φ) v c hc).trans (hZ.fix φ v c hc)⟩

theorem IsFix.inv {C : Type*} {act : C → Prop} {Z : Equiv.Perm (Fn K C)}
    (hZ : IsFix act Z) : IsFix act Z⁻¹ := by
  refine ⟨fun φ ψ ↦ ?_, fun φ v c hc ↦ ?_⟩
  · apply Z.injective
    rw [hZ.add, perm_apply_inv_self, perm_apply_inv_self, perm_apply_inv_self]
  · have h := hZ.fix (Z⁻¹ φ) v c hc
    rw [perm_apply_inv_self] at h
    exact h.symm

/-- The subgroup of additive permutations that are the identity at inactive classes. -/
def fixSub {C : Type*} (act : C → Prop) : Subgroup (Equiv.Perm (Fn K C)) where
  carrier := {Z | IsFix act Z}
  mul_mem' := fun hY hZ ↦ IsFix.mul hY hZ
  one_mem' := IsFix.one act
  inv_mem' := fun hZ ↦ IsFix.inv hZ

theorem mem_fixSub {C : Type*} {act : C → Prop} {Z : Equiv.Perm (Fn K C)} :
    Z ∈ fixSub act ↔ IsFix act Z := Iff.rfl

theorem isFix_permL {C : Type*} (n : Fin K) (act : C → Prop) [DecidablePred act]
    (σ : C → C) (T T' : Tab) (hσ : ∀ c, act (σ c) ↔ act c)
    (hT : ∀ t g h y, T'.app t (fun s ↦ T.app s g (h s)) (T.app t h y) = g t)
    (hT' : ∀ t g h y, T.app t (fun s ↦ T'.app s g (h s)) (T'.app t h y) = g t) :
    IsFix act (permL n act σ T T' hσ hT hT') :=
  ⟨fun φ ψ ↦ opL_add n act σ T φ ψ, fun φ v _ hc ↦ opL_of_not n act σ T φ v hc⟩

theorem opP_fix {C : Type*} {act : C → Prop} [DecidablePred act] {β : C → C}
    {Z : Equiv.Perm (Fn K C)} (hβ : ∀ c, act c → ¬ act (β c)) (hZ : IsFix act Z)
    (φ : Fn K C) : opP act β (Z φ) = opP act β φ := by
  funext v c
  by_cases hc : act c
  · simp only [opP, hc, ↓reduceIte]
    exact hZ.fix φ v (β c) (hβ c hc)
  · simp only [opP, hc, ↓reduceIte]

section G3

variable {C : Type*} (n : Fin K) (act : C → Prop) [DecidablePred act] (σ : C → C)
  (β : C → C)

/-- The operator form of G3 a) and G4 a): `B^{a⁻¹} B⁻¹ = B^{(a')⁻¹}` (KMS `l789`). -/
theorem g3a_of {a a' B : Equiv.Perm (Fn K C)} {T Ti T' T'i : Tab}
    (hσ : ∀ c, act (σ c) ↔ act c) (hβ : ∀ c, act c → ¬ act (β c))
    (ha : ∀ φ, a φ = opL n act σ T φ) (hai : ∀ φ, a⁻¹ φ = opL n act σ Ti φ)
    (hap : ∀ φ, a' φ = opL n act σ T' φ) (hapi : ∀ φ, a'⁻¹ φ = opL n act σ T'i φ)
    (hB : ∀ φ, B φ = opB act β φ) (hBi : ∀ φ, B⁻¹ φ = opB act β φ)
    (hTi : ∀ t g h y, T.app t (fun s ↦ Ti.app s g (h s)) (Ti.app t h y) = g t)
    (hT'i : ∀ t g h y, T'.app t (fun s ↦ T'i.app s g (h s)) (T'i.app t h y) = g t)
    (hT' : ∀ t g y, T'.app t g y = T.app t g y + g t) :
    khConj B a⁻¹ * B⁻¹ * (khConj B a'⁻¹)⁻¹ = 1 := by
  rw [mul_inv_eq_one]
  refine Equiv.ext fun φ ↦ ?_
  simp only [khConj, inv_inv, Equiv.Perm.mul_apply, ha, hai, hap, hapi, hB, hBi, opB_eq,
    opL_add, opP_add, opP_opL act β hβ, opP_opP act β hβ, add_zero,
    opL_opL n act σ hσ hTi, opL_opL n act σ hσ hT'i]
  rw [opL_eq_add n act σ T T' hT' (opP act β φ) (fun v _ hc ↦ opP_of_not act β φ v hc)]
  abel

/-- The operator form of G3 b), c) and G4 b): `[B^Z, B] = 1` for `Z ∈ fixSub act`
(KMS `l789`). -/
theorem g3b_of {B Z : Equiv.Perm (Fn K C)} (hβ : ∀ c, act c → ¬ act (β c))
    (hB : ∀ φ, B φ = opB act β φ) (hZ : IsFix act Z) : khComm (khConj B Z) B = 1 := by
  apply khComm_eq_one_of_mul_comm
  have hZi : IsFix act Z⁻¹ := hZ.inv
  refine Equiv.ext fun φ ↦ ?_
  simp only [khConj, Equiv.Perm.mul_apply, hB, opB_eq, hZ.add, hZi.add, opP_add,
    opP_fix hβ hZ, opP_fix hβ hZi, opP_opP act β hβ, add_zero, perm_inv_apply_self]
  abel

end G3

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
