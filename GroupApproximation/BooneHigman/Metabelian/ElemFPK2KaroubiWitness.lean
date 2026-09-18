import Mathlib.GroupTheory.GroupAction.ConjAct
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelInj
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical action witness

Lane `bh-met-91v`, witness module.  Notation: `P = A ×_L L[X]`, `L = A_s`,
`K = ker (fst : St(M, P) → St(M, A))`.

* `k2Karoubi_kerB s M = ker (ev₀ : St(M, L[X]) → St(M, L))`, a normal subgroup.
* `k2Karoubi_q : K →* kerB`, `y ↦ snd y` (well defined since `ev₀ ∘ snd = λ ∘ fst`).
* `k2Karoubi_alpha : St(M, L) →* MulAut kerB`, `d ↦ conjugation by C d`.
* `k2Karoubi_F1`, `k2Karoubi_F2`, `k2Karoubi_F3`, `k2Karoubi_Compat`: the root formulas and the
  compatibility hold **unconditionally**, by the Steinberg relations in `St(M, L[X])`.
* `k2Karoubi_faithful_of_inj`: faithfulness of this witness is exactly `R1` at level `M`
  (`fst y = 1` and `snd y = 1` imply that `y` dies after padding).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KaroubiGroup

/-- If `a b = e b a` and `e` commutes with `a`, then `b a b⁻¹ = a e⁻¹`. -/
theorem k2Karoubi_conj_of_comm {G : Type*} [Group G] {a b e : G} (hc : a * b = e * b * a)
    (he : e * a = a * e) : b * a * b⁻¹ = a * e⁻¹ := by
  have h1 : e = a * b * a⁻¹ * b⁻¹ := by
    rw [hc]
    group
  have h2 : e⁻¹ * a = a * e⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, he, mul_inv_cancel_right]
  rw [← h2, h1]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_conj_of_comm

end KaroubiGroup

section KaroubiWitness

variable {A : Type*} [CommRing A] {s : A} {M : ℕ}

/-- `ker (ev₀ : St(M, L[X]) → St(M, L))`. -/
def k2Karoubi_kerB (s : A) (M : ℕ) :
    Subgroup (SteinbergGroup (Fin M) (Polynomial (Localization.Away s))) :=
  (ringMap (Polynomial.evalRingHom (0 : Localization.Away s))).ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_kerB

instance k2Karoubi_kerB_normal : (k2Karoubi_kerB s M).Normal :=
  MonoidHom.normal_ker (ringMap (Polynomial.evalRingHom (0 : Localization.Away s)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_kerB_normal

theorem k2Karoubi_mem_kerB {z : SteinbergGroup (Fin M) (Polynomial (Localization.Away s))} :
    z ∈ k2Karoubi_kerB s M ↔ ringMap (Polynomial.evalRingHom (0 : Localization.Away s)) z = 1 :=
  MonoidHom.mem_ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_mem_kerB

/-- `ev₀ ∘ snd = λ ∘ fst` on `P`. -/
theorem k2Karoubi_evalZero_comp_snd (s : A) :
    (Polynomial.evalRingHom (0 : Localization.Away s)).comp (k2PullRel_snd s) =
      (algebraMap A (Localization.Away s)).comp (k2PullRel_fst s) :=
  RingHom.ext fun b ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_evalRingHom]
    exact k2PullRel_eval_snd b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_evalZero_comp_snd

theorem k2Karoubi_snd_mem {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (hy : y ∈ k2PullRel_ker s M) : ringMap (k2PullRel_snd s) y ∈ k2Karoubi_kerB s M := by
  rw [k2PullRel_mem_ker] at hy
  rw [k2Karoubi_mem_kerB, ringMap_ringMap, k2Karoubi_evalZero_comp_snd, ← ringMap_ringMap, hy,
    map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_snd_mem

/-- `q y = snd y`. -/
noncomputable def k2Karoubi_q (s : A) (M : ℕ) : k2PullRel_ker s M →* k2Karoubi_kerB s M where
  toFun y := ⟨ringMap (k2PullRel_snd s) y, k2Karoubi_snd_mem y.2⟩
  map_one' := Subtype.ext (map_one (ringMap (k2PullRel_snd s)))
  map_mul' a b := Subtype.ext (map_mul (ringMap (k2PullRel_snd s)) a b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_q

/-- `α d = conjugation by C d`. -/
noncomputable def k2Karoubi_alpha (s : A) (M : ℕ) :
    SteinbergGroup (Fin M) (Localization.Away s) →* MulAut (k2Karoubi_kerB s M) :=
  (MulAut.conjNormal (H := k2Karoubi_kerB s M)).comp (ringMap Polynomial.C)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_alpha

theorem k2Karoubi_coe_q (y : k2PullRel_ker s M) :
    ((k2Karoubi_q s M y : k2Karoubi_kerB s M) :
        SteinbergGroup (Fin M) (Polynomial (Localization.Away s))) =
      ringMap (k2PullRel_snd s) y :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_coe_q

theorem k2Karoubi_coe_alpha (d : SteinbergGroup (Fin M) (Localization.Away s))
    (z : k2Karoubi_kerB s M) :
    ((k2Karoubi_alpha s M d z : k2Karoubi_kerB s M) :
        SteinbergGroup (Fin M) (Polynomial (Localization.Away s))) =
      ringMap Polynomial.C d * z * (ringMap Polynomial.C d)⁻¹ :=
  MulAut.conjNormal_apply (ringMap Polynomial.C d) z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_coe_alpha

theorem k2Karoubi_coe_u (i j : Fin M) (hij : i ≠ j) (h : Polynomial (Localization.Away s)) :
    ((k2PullRel_u (k2Karoubi_q s M) i j hij h : k2Karoubi_kerB s M) :
        SteinbergGroup (Fin M) (Polynomial (Localization.Away s))) =
      x i j hij (h - Polynomial.C (h.eval 0)) := by
  show ringMap (k2PullRel_snd s) (x i j hij (k2PullRel_lift s h)) = _
  rw [ringMap_x, k2PullRel_snd_lift]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_coe_u

/-- `F1` for the canonical witness. -/
theorem k2Karoubi_F1 : k2PullRel_F1 (k2Karoubi_q s M) (k2Karoubi_alpha s M) := by
  intro i j k l hij hkl hjk hli _ _
  apply Subtype.ext
  rw [k2Karoubi_coe_alpha, k2Karoubi_coe_u, ringMap_x,
    (x_commute_of_ne k l i j hkl hij hli hjk _ _).eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_F1

/-- `F2` for the canonical witness. -/
theorem k2Karoubi_F2 : k2PullRel_F2 (k2Karoubi_q s M) (k2Karoubi_alpha s M) := by
  intro i j k hij hjk hik t h
  apply Subtype.ext
  simp only [Subgroup.coe_mul, k2Karoubi_coe_alpha, k2Karoubi_coe_u, ringMap_x]
  rw [mul_inv_eq_iff_eq_mul]
  have e : Polynomial.C t * h - Polynomial.C ((Polynomial.C t * h).eval 0) =
      Polynomial.C t * (h - Polynomial.C (h.eval 0)) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, map_mul]
    ring
  rw [e]
  exact (k2PullRel_comm_iff _ _ _).mp (x_commutator i j k hij hjk hik _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_F2

/-- `F3` for the canonical witness. -/
theorem k2Karoubi_F3 : k2PullRel_F3 (k2Karoubi_q s M) (k2Karoubi_alpha s M) := by
  intro i j k hij hjk hik t h
  apply Subtype.ext
  simp only [Subgroup.coe_mul, k2Karoubi_coe_alpha, k2Karoubi_coe_u, ringMap_x]
  have e : -(h * Polynomial.C t) - Polynomial.C ((-(h * Polynomial.C t)).eval 0) =
      -((h - Polynomial.C (h.eval 0)) * Polynomial.C t) := by
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C, map_neg, map_mul]
    ring
  rw [e, x_neg]
  exact k2Karoubi_conj_of_comm
    ((k2PullRel_comm_iff _ _ _).mp (x_commutator i j k hij hjk hik _ _))
    (x_commute_of_ne i k i j hik hij hik.symm hij.symm _ _).eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_F3

/-- `Compat` for the canonical witness. -/
theorem k2Karoubi_Compat : k2PullRel_Compat (k2Karoubi_q s M) (k2Karoubi_alpha s M) := by
  intro c i j hij b _
  apply Subtype.ext
  rw [k2Karoubi_coe_alpha]
  show _ * ringMap (k2PullRel_snd s) (x i j hij b) * _ =
    ringMap (k2PullRel_snd s)
      (ringMap (k2PullRel_const s) c * x i j hij b * (ringMap (k2PullRel_const s) c)⁻¹)
  rw [map_mul, map_mul, map_inv, k2PullRel_ringMap_snd_const]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_Compat

/-- **Faithfulness of the canonical witness is `R1` at level `M`**. -/
theorem k2Karoubi_faithful_of_inj
    (h : ∀ y : SteinbergGroup (Fin M) (k2DilateSt_pullback s),
      ringMap (k2PullRel_fst s) y = 1 → ringMap (k2PullRel_snd s) y = 1 →
        cubeDiagDilate_StDies y) :
    k2PullRel_Faithful (k2Karoubi_q s M) := fun y hy ↦
  h y (k2PullRel_mem_ker.mp y.2) (congrArg Subtype.val hy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_faithful_of_inj

end KaroubiWitness

end GroupApproximation.BooneHigman.Metabelian.ElemFP
