import GroupApproximation.CharClass.LIXKLocalRestrict
import GroupApproximation.CharClass.LIXKStepCWired
import GroupApproximation.CharClass.LIXChartIso
import GroupApproximation.CharClass.LIXHclass
import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv
import GroupApproximation.CharClass.ThomProjectivePunctured
import GroupApproximation.CharClass.ThomKunnethProjective
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C with `k` zeros at the LIX objects, over `F₂`: one open field, and the exponent form

Lane `lix-oddside` of the stronger Problem LIX program
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4).

`CharClass/LIXKStepCWired.lean`'s `lixK_topClass_ne_zero` carries seven open fields.  At mod-2
coefficients all but one are closed here:

* `hsplit` and `hloc` — `CharClass/LIXKLocalRestrict.lean` (relative Mayer–Vietoris, and an
  `F₂`-line has one nonzero element);
* `hacyclic` at every zero — `puncturedAcyclic_lixPoint` with its producers;
* `absLine` — `nonempty_absEquiv_lix`;
* `exc`, `chartIso` at every zero — a unitary of `ℂ³` carrying `−e₃` to the `j`-th zero
  (`kSwapHomeo`), then the one-zero `lixRelModelIso`;
* `hclass` — `lixHclass`, which holds for every `G`.

What remains is `KLocalNonzero`: near each zero, on a set containing no other zero, the pulled
back Thom class restricts nontrivially.  That is the one-zero local computation run at `z_j`.

## The exponent

The internal index `k` has `k + 1` zeros (`joinC k` has degree `k + 1`).  The fleet ruling of
2026-09-11 indexes Lemma 2 by the exponent `e`, i.e. the section `bVecK (e − 1)` with `e` zeros.
`lixK_topChern_ne_zero_exponent` is that form: for odd `e`, `γ_r = e · c ≠ 0`.

## Main declarations

* `kSwapHomeo`, `lixKSwap`, `lixKExc` — the excision data at every zero.
* `KLocalNonzero` — the remaining local field, named.
* `lixK_topChern_ne_zero_of_localNonzero` — **Step C with `k + 1` zeros over `F₂`**.
* `lixK_topChern_ne_zero_exponent` — the same, indexed by the exponent `e = k + 1`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. A unitary carrying `−e₃` to the `j`-th zero -/

/-- `(x₀, x₁, x₂) ↦ (−ζⱼ x₂, x₁, x₀)`. -/
def kSwapVec (k : ℕ) (j : Fin (k + 1)) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  Function.update (Function.update x 0 (-(kRoot k j * x 2))) 2 (x 0)

/-- `(y₀, y₁, y₂) ↦ (y₂, y₁, −ζⱼ⁻¹ y₀)`. -/
def kSwapInvVec (k : ℕ) (j : Fin (k + 1)) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  Function.update (Function.update y 0 (y 2)) 2 (-((kRoot k j)⁻¹ * y 0))

theorem kSwapVec_apply_zero (k : ℕ) (j : Fin (k + 1)) (x : Fin 3 → ℂ) :
    kSwapVec k j x 0 = -(kRoot k j * x 2) := by
  rw [kSwapVec, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2), Function.update_self]

theorem kSwapVec_apply_one (k : ℕ) (j : Fin (k + 1)) (x : Fin 3 → ℂ) :
    kSwapVec k j x 1 = x 1 := by
  rw [kSwapVec, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]

theorem kSwapVec_apply_two (k : ℕ) (j : Fin (k + 1)) (x : Fin 3 → ℂ) :
    kSwapVec k j x 2 = x 0 := by
  rw [kSwapVec, Function.update_self]

theorem kSwapInvVec_apply_zero (k : ℕ) (j : Fin (k + 1)) (y : Fin 3 → ℂ) :
    kSwapInvVec k j y 0 = y 2 := by
  rw [kSwapInvVec, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2), Function.update_self]

theorem kSwapInvVec_apply_one (k : ℕ) (j : Fin (k + 1)) (y : Fin 3 → ℂ) :
    kSwapInvVec k j y 1 = y 1 := by
  rw [kSwapInvVec, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]

theorem kSwapInvVec_apply_two (k : ℕ) (j : Fin (k + 1)) (y : Fin 3 → ℂ) :
    kSwapInvVec k j y 2 = -((kRoot k j)⁻¹ * y 0) := by
  rw [kSwapInvVec, Function.update_self]

theorem kSwap_vec_ext {x y : Fin 3 → ℂ} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem kSwapInvVec_kSwapVec (k : ℕ) (j : Fin (k + 1)) (x : Fin 3 → ℂ) :
    kSwapInvVec k j (kSwapVec k j x) = x := by
  refine kSwap_vec_ext ?_ ?_ ?_
  · rw [kSwapInvVec_apply_zero, kSwapVec_apply_two]
  · rw [kSwapInvVec_apply_one, kSwapVec_apply_one]
  · rw [kSwapInvVec_apply_two, kSwapVec_apply_zero, mul_neg, neg_neg,
      inv_mul_cancel_left₀ (kRoot_ne_zero k j)]

theorem kSwapVec_kSwapInvVec (k : ℕ) (j : Fin (k + 1)) (y : Fin 3 → ℂ) :
    kSwapVec k j (kSwapInvVec k j y) = y := by
  refine kSwap_vec_ext ?_ ?_ ?_
  · rw [kSwapVec_apply_zero, kSwapInvVec_apply_two, mul_neg, neg_neg,
      mul_inv_cancel_left₀ (kRoot_ne_zero k j)]
  · rw [kSwapVec_apply_one, kSwapInvVec_apply_one]
  · rw [kSwapVec_apply_two, kSwapInvVec_apply_zero]

theorem kSwapVec_mem {k : ℕ} (j : Fin (k + 1)) {x : Fin 3 → ℂ}
    (hx : x ∈ unitVectors (Fin 3)) : kSwapVec k j x ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, Fin.sum_univ_three] at hx ⊢
  rw [kSwapVec_apply_zero, kSwapVec_apply_one, kSwapVec_apply_two, norm_neg, norm_mul,
    norm_kRoot, one_mul]
  linarith

theorem kSwapInvVec_mem {k : ℕ} (j : Fin (k + 1)) {y : Fin 3 → ℂ}
    (hy : y ∈ unitVectors (Fin 3)) : kSwapInvVec k j y ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, Fin.sum_univ_three] at hy ⊢
  rw [kSwapInvVec_apply_zero, kSwapInvVec_apply_one, kSwapInvVec_apply_two, norm_neg,
    norm_mul, norm_inv, norm_kRoot, inv_one, one_mul]
  linarith

theorem continuous_kSwapVec (k : ℕ) (j : Fin (k + 1)) : Continuous (kSwapVec k j) := by
  have h0 : Continuous fun x : Fin 3 → ℂ => -(kRoot k j * x 2) :=
    (continuous_const.mul (continuous_apply 2)).neg
  exact (continuous_id.update 0 h0).update 2 (continuous_apply 0)

theorem continuous_kSwapInvVec (k : ℕ) (j : Fin (k + 1)) : Continuous (kSwapInvVec k j) := by
  have h2 : Continuous fun y : Fin 3 → ℂ => -((kRoot k j)⁻¹ * y 0) :=
    (continuous_const.mul (continuous_apply 0)).neg
  exact (continuous_id.update 0 (continuous_apply 2)).update 2 h2

/-- **The unitary of `S⁵` carrying `−e₃` to the `j`-th zero**, as a homeomorphism. -/
def kSwapHomeo (k : ℕ) (j : Fin (k + 1)) :
    ↥(unitVectors (Fin 3)) ≃ₜ ↥(unitVectors (Fin 3)) where
  toFun x := ⟨kSwapVec k j x, kSwapVec_mem j x.2⟩
  invFun y := ⟨kSwapInvVec k j y, kSwapInvVec_mem j y.2⟩
  left_inv x := Subtype.ext (kSwapInvVec_kSwapVec k j x)
  right_inv y := Subtype.ext (kSwapVec_kSwapInvVec k j y)
  continuous_toFun := ((continuous_kSwapVec k j).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_kSwapInvVec k j).comp continuous_subtype_val).subtype_mk _

theorem kSwapHomeo_negEThree (k : ℕ) (j : Fin (k + 1)) :
    kSwapHomeo k j negEThree = kZero k j := by
  refine Subtype.ext (kSwap_vec_ext ?_ ?_ ?_)
  · show kSwapVec k j (fun i => -eThree i) 0 = kZeroVec k j 0
    rw [kSwapVec_apply_zero, kZeroVec_apply_zero]
    simp [eThree]
  · show kSwapVec k j (fun i => -eThree i) 1 = kZeroVec k j 1
    rw [kSwapVec_apply_one, kZeroVec_apply_one]
    simp [eThree]
  · show kSwapVec k j (fun i => -eThree i) 2 = kZeroVec k j 2
    rw [kSwapVec_apply_two, kZeroVec_apply_two]
    simp [eThree]

/-- The same unitary on `N = S¹ × S⁵ × Y`, acting on the sphere factor only. -/
def lixKSwap (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    (↥sphereOne × baseM dd) ≃ₜ (↥sphereOne × baseM dd) :=
  (Homeomorph.refl ↥sphereOne).prodCongr
    ((kSwapHomeo k j).prodCongr (Homeomorph.refl (baseY dd)))

theorem lixKSwap_lixZero (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    lixKSwap k dd j (lixZero dd) = lixKZero k dd j := by
  show ((southPole : ↥sphereOne), (kSwapHomeo k j negEThree, baseYPoint dd))
    = (southPole, (kZero k j, baseYPoint dd))
  rw [kSwapHomeo_negEThree]

theorem lixKSwap_symm_image (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) :
    (lixKSwap k dd j).symm '' ({lixKZero k dd j}ᶜ : Set (↥sphereOne × baseM dd))
      = ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩ hp
    refine hq ?_
    have h1 : (lixKSwap k dd j).symm q = lixZero dd := hp
    exact Set.mem_singleton_iff.mpr
      (by rw [← lixKSwap_lixZero k dd j, ← h1, Homeomorph.apply_symm_apply])
  · intro hp
    refine ⟨lixKSwap k dd j p, ?_, Homeomorph.symm_apply_apply _ _⟩
    intro hq
    refine hp ?_
    have h1 : lixKSwap k dd j p = lixKZero k dd j := hq
    rw [← lixKSwap_lixZero k dd j] at h1
    exact (lixKSwap k dd j).injective h1

/-- **The excision data at the `j`-th zero**: the pair punctured at `z_j` is the pair punctured
at the one-zero point, through the unitary. -/
def lixKExc (k : ℕ) (dd : Fin ℓ → ℕ) (j : Fin (k + 1)) (n : ℕ) :
    relCohomology (ZMod 2) (lixN dd) ({lixKZero k dd j}ᶜ : Set (↥sphereOne × baseM dd)) n
      ≅ relCohomology (ZMod 2) (lixN dd) ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) n :=
  relCohomologyCongr (lixKSwap k dd j).symm _ _ (lixKSwap_symm_image k dd j) n

theorem lixKZeroSet_compl_iff (k : ℕ) (dd : Fin ℓ → ℕ) (y : ↥sphereOne × baseM dd) :
    y ∈ ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) ↔ ∀ i, y ≠ lixKZero k dd i := by
  rw [Set.mem_compl_iff, mem_lixKZeroSet_iff, not_exists]

/-! ## 2. The remaining local field -/

/-- **The one-zero local computation, at every zero.**  For each zero `z_i` there is a set
containing `z_i` and no other zero on which the section's pull back of the Thom class restricts
nontrivially.

At `k = 0` the zero is `(southPole, (−e₁, basePoint))` and this is the existing one-zero
computation with the constant section at `e₁` (sp-oddside-n's chart construction: in the chart
`κ_j`-composed at `z_j`, the section is `trivialBlockChart` at every `j`). -/
def KLocalNonzero (k : ℕ) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × baseM dd),
    (∀ j, j ≠ i → lixKZero k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo (ZMod 2) (X := lixN dd) B
          ((lixKZeroSet k dd)ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd)).hom
        ((lixKSRel k hGc hGu hGe (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu)) ≠ 0

/-! ## 3. Step C with `k + 1` zeros over `F₂` -/

/-- **Step C's odd side with `k + 1` zeros, at the LIX objects, over `F₂`.**  For every `G`
with Step A's seam `G (e₁, 0) = (Ψ_k x, 0)`, if `k + 1` is odd and the local computation holds
at every zero, the top mod-2 Chern class of `W_g` is nonzero.

Every field of `lixK_topClass_ne_zero` except the local one is closed here. -/
theorem lixK_topChern_ne_zero_of_localNonzero (k : ℕ) (hdd : ∀ j, 0 < dd j)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK k m) 0)
    (hodd : Odd (k + 1)) (hlocal : KLocalNonzero k hGc hGu hGe) :
    lixChern dd (mappingTorus Vmat G circHoriz circHeight) (continuous_mappingTorus_lix hGc)
      (isStarProjection_mappingTorus_lix hGu) (lixRank dd) ≠ 0 := by
  have hgamma := topClass_eq_of_naturality'
    (RelativeSupport.lixJE hGc hGu (2 * lixRank dd)) (lixKJ k dd (2 * lixRank dd))
    (lixKSRel k hGc hGu hGe (2 * lixRank dd)) (lixKSAbs k hGc hGu hGe (2 * lixRank dd))
    (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd))
    (lixK_hnat k hGc hGu hGe (2 * lixRank dd)) (lixK_hsection k hGc hGu hGe (2 * lixRank dd))
    (lixHclass hGc hGu (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu))
  rw [← hgamma]
  exact LIXKRelMV.topChernClass_ne_zero_kzero_two_of_restrict
    (N := ↥sphereOne × baseM dd) (r := lixRank dd) 0 (lixKZero k dd)
    (lixKZero_injective k dd) (lixKZeroSet_compl_iff k dd)
    (fun i => puncturedAcyclic_lixPoint puncturedAcyclic_CP (fun d _ => kunnethFactor_CP d)
      kunnethFactor_CP_punctured hbase_lix hdd (lixKZero k dd i))
    (nonempty_absEquiv_lix dd hdd)
    (fun i => lixKExc k dd i (2 * lixRank dd))
    (fun _ => lixRelModelIso dd (2 * lixRank dd))
    _ (fun i => (hlocal i).choose) (fun i => (hlocal i).choose_spec.1)
    (fun i => (hlocal i).choose_spec.2) (natCast_ne_zero_zmod_two hodd)

/-- **The exponent form** (fleet ruling 2026-09-11): the section of exponent `e` is
`bVecK (e − 1)`, with `e` zeros, and for odd `e` its top class `γ_r = e · c` is nonzero. -/
theorem lixK_topChern_ne_zero_exponent (e : ℕ) (he : 1 ≤ e) (hodd : Odd e)
    (hdd : ∀ j, 0 < dd j) (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK m) 0 = Sum.elim (bVecK (e - 1) m) 0)
    (hlocal : KLocalNonzero (e - 1) hGc hGu hGe) :
    lixChern dd (mappingTorus Vmat G circHoriz circHeight) (continuous_mappingTorus_lix hGc)
      (isStarProjection_mappingTorus_lix hGu) (lixRank dd) ≠ 0 :=
  lixK_topChern_ne_zero_of_localNonzero (e - 1) hdd hGc hGu hGe
    (by rwa [Nat.sub_add_cancel he]) hlocal

/-! Audited on every build. -/

#audit_axioms kSwapHomeo_negEThree
#audit_axioms lixKSwap_symm_image
#audit_axioms lixK_topChern_ne_zero_of_localNonzero
#audit_axioms lixK_topChern_ne_zero_exponent

end GroupApproximation.CharClass
