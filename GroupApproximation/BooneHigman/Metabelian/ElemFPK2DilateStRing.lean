import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateProj
import GroupApproximation.Meta.AxiomGuard

/-!
# The pullback ring of the dilation colimit

Lane `bh-met-90s`, ring module.  Let `A` be a commutative ring, `s ∈ A`, `L = A_s`,
`λ : A → L`, `u = 1/s ∈ L` and `μ_c = k2CubeDilate_scale A c` (`X ↦ c X`).

* `k2DilateSt_pullback s = P = A ×_L L[X]`, the pairs `(a, h)` with `λ a = h(0)`.
* `k2DilateSt_stage s k : A[X] → A × L[X]`, `f ↦ (f(0), (λ f)(u^k X))`.  It lands in `P`, and
  `k2DilateSt_toPullback s k : A[X] → P` is its corestriction.
* `k2DilateSt_stage_comp_scale`: `ι_{k+t} ∘ μ_{s^t} = ι_k`.  So the `ι_k` form a cocone on the
  sequence `A[X] → A[X] → ⋯` of dilations by `s`.
* `k2DilateSt_eventually_of_stage`: the kernel of `ι_k` is killed by a dilation.  If
  `ι_k h = 0` then `h(0) = 0` and `λ h = 0` (dilation by `u^k` is invertible over `L`), so
  `μ_{s^r} h = 0` for all large `r` (`k2Dilate_scale_eq_zero`).

Everything is ring theory; no Steinberg relation is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section DilateStRing

variable {A : Type*} [CommRing A]

/-- `u = 1/s` in `A_s`. -/
noncomputable def k2DilateSt_inv (s : A) : Localization.Away s :=
  IsLocalization.Away.invSelf (S := Localization.Away s) s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_inv

theorem k2DilateSt_mul_inv (s : A) :
    algebraMap A (Localization.Away s) s * k2DilateSt_inv s = 1 :=
  IsLocalization.Away.mul_invSelf s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_mul_inv

theorem k2DilateSt_inv_mul (s : A) :
    k2DilateSt_inv s * algebraMap A (Localization.Away s) s = 1 := by
  rw [mul_comm, k2DilateSt_mul_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_inv_mul

/-- `λ(s)^t u^{k+t} = u^k`. -/
theorem k2DilateSt_pow_mul_inv_pow (s : A) (k t : ℕ) :
    algebraMap A (Localization.Away s) s ^ t * k2DilateSt_inv s ^ (k + t) =
      k2DilateSt_inv s ^ k := by
  rw [pow_add (k2DilateSt_inv s) k t, mul_left_comm, ← mul_pow, k2DilateSt_mul_inv, one_pow,
    mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_pow_mul_inv_pow

/-- The stage map `ι_k : A[X] → A × L[X]`, `f ↦ (f(0), (λ f)(u^k X))`. -/
noncomputable def k2DilateSt_stage (s : A) (k : ℕ) :
    Polynomial A →+* A × Polynomial (Localization.Away s) :=
  RingHom.prod (Polynomial.evalRingHom 0)
    ((k2CubeDilate_scale (Localization.Away s) (k2DilateSt_inv s ^ k)).comp
      (Polynomial.mapRingHom (algebraMap A (Localization.Away s))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage

theorem k2DilateSt_stage_apply (s : A) (k : ℕ) (f : Polynomial A) :
    k2DilateSt_stage s k f = (f.eval 0, k2CubeDilate_scale (Localization.Away s)
      (k2DilateSt_inv s ^ k) (f.map (algebraMap A (Localization.Away s)))) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_apply

theorem k2DilateSt_stage_fst (s : A) (k : ℕ) (f : Polynomial A) :
    (k2DilateSt_stage s k f).1 = f.eval 0 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_fst

theorem k2DilateSt_stage_snd (s : A) (k : ℕ) (f : Polynomial A) :
    (k2DilateSt_stage s k f).2 = k2CubeDilate_scale (Localization.Away s)
      (k2DilateSt_inv s ^ k) (f.map (algebraMap A (Localization.Away s))) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_snd

theorem k2DilateSt_stage_C (s : A) (k : ℕ) (a : A) :
    k2DilateSt_stage s k (Polynomial.C a) =
      (a, Polynomial.C (algebraMap A (Localization.Away s) a)) := by
  rw [k2DilateSt_stage_apply, Polynomial.eval_C, Polynomial.map_C, k2CubeDilate_scale_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_C

theorem k2DilateSt_stage_X (s : A) (k : ℕ) :
    k2DilateSt_stage s k Polynomial.X =
      (0, Polynomial.C (k2DilateSt_inv s ^ k) * Polynomial.X) := by
  rw [k2DilateSt_stage_apply, Polynomial.eval_X, Polynomial.map_X, k2CubeDilate_scale_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_X

/-- **Cocone**: `ι_{k+t} ∘ μ_{s^t} = ι_k`. -/
theorem k2DilateSt_stage_comp_scale (s : A) (k t : ℕ) :
    (k2DilateSt_stage s (k + t)).comp (k2CubeDilate_scale A (s ^ t)) = k2DilateSt_stage s k :=
  Polynomial.ringHom_ext
    (fun a ↦ by
      rw [RingHom.comp_apply, k2CubeDilate_scale_C, k2DilateSt_stage_C, k2DilateSt_stage_C])
    (by
      rw [RingHom.comp_apply, k2CubeDilate_scale_X, map_mul, k2DilateSt_stage_C,
        k2DilateSt_stage_X, k2DilateSt_stage_X, Prod.mk_mul_mk, mul_zero, ← mul_assoc,
        ← Polynomial.C_mul, map_pow (algebraMap A (Localization.Away s)) s t,
        k2DilateSt_pow_mul_inv_pow])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_comp_scale

theorem k2DilateSt_stage_scale (s : A) (k t : ℕ) (f : Polynomial A) :
    k2DilateSt_stage s (k + t) (k2CubeDilate_scale A (s ^ t) f) = k2DilateSt_stage s k f :=
  DFunLike.congr_fun (k2DilateSt_stage_comp_scale s k t) f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_scale

/-- `μ_{s^a} ∘ μ_{s^b} = μ_{s^{b+a}}`, pointwise. -/
theorem k2DilateSt_scale_scale (s : A) (a b : ℕ) (f : Polynomial A) :
    k2CubeDilate_scale A (s ^ a) (k2CubeDilate_scale A (s ^ b) f) =
      k2CubeDilate_scale A (s ^ (b + a)) f := by
  rw [pow_add s b a]
  exact DFunLike.congr_fun (k2Dilate_scale_comp (s ^ a) (s ^ b)) f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_scale_scale

/-- `(μ_c h)(0) = h(0)`. -/
theorem k2DilateSt_evalZero_scale {T : Type*} [CommRing T] (c : T) (h : Polynomial T) :
    (k2CubeDilate_scale T c h).eval 0 = h.eval 0 :=
  DFunLike.congr_fun (k2Dilate_evalZero_comp_scale c) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_evalZero_scale

/-- Dilation by `λ(s)^k` undoes dilation by `u^k` over `L`. -/
theorem k2DilateSt_scale_inv_cancel (s : A) (k : ℕ) (h : Polynomial (Localization.Away s)) :
    k2CubeDilate_scale (Localization.Away s) (algebraMap A (Localization.Away s) s ^ k)
      (k2CubeDilate_scale (Localization.Away s) (k2DilateSt_inv s ^ k) h) = h := by
  have e := DFunLike.congr_fun (k2Dilate_scale_comp
    (algebraMap A (Localization.Away s) s ^ k) (k2DilateSt_inv s ^ k)) h
  rw [RingHom.comp_apply, ← mul_pow, k2DilateSt_inv_mul, one_pow, k2CubeDilate_scale_one,
    RingHom.id_apply] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_scale_inv_cancel

/-- **The kernel of a stage map.**  If `ι_k h = 0` then `h(0) = 0` and `λ h = 0`. -/
theorem k2DilateSt_map_eq_zero_of_stage {s : A} {k : ℕ} {h : Polynomial A}
    (hh : k2DilateSt_stage s k h = 0) :
    h.coeff 0 = 0 ∧ Polynomial.map (algebraMap A (Localization.Away s)) h = 0 := by
  have h1 := congrArg Prod.fst hh
  have h2 := congrArg Prod.snd hh
  rw [k2DilateSt_stage_fst, Prod.fst_zero] at h1
  rw [k2DilateSt_stage_snd, Prod.snd_zero] at h2
  refine ⟨by rw [Polynomial.coeff_zero_eq_eval_zero]; exact h1, ?_⟩
  rw [← k2DilateSt_scale_inv_cancel s k (Polynomial.map (algebraMap A _) h), h2, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_map_eq_zero_of_stage

/-- **The kernel of a stage map is killed by dilation.** -/
theorem k2DilateSt_eventually_of_stage {s : A} {k : ℕ} {h : Polynomial A}
    (hh : k2DilateSt_stage s k h = 0) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r → k2CubeDilate_scale A (s ^ r) h = 0 :=
  k2Dilate_scale_eq_zero s h (k2DilateSt_map_eq_zero_of_stage hh).1
    (k2DilateSt_map_eq_zero_of_stage hh).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_eventually_of_stage

end DilateStRing

section DilateStPullback

variable {A : Type*} [CommRing A]

/-- **The pullback** `P = A ×_L L[X] = {(a, h) : λ a = h(0)}`. -/
def k2DilateSt_pullback (s : A) : Subring (A × Polynomial (Localization.Away s)) :=
  RingHom.eqLocus ((algebraMap A (Localization.Away s)).comp
      (RingHom.fst A (Polynomial (Localization.Away s))))
    ((Polynomial.evalRingHom 0).comp (RingHom.snd A (Polynomial (Localization.Away s))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_pullback

theorem k2DilateSt_mem_pullback (s : A) (q : A × Polynomial (Localization.Away s)) :
    q ∈ k2DilateSt_pullback s ↔ algebraMap A (Localization.Away s) q.1 = q.2.eval 0 :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_mem_pullback

theorem k2DilateSt_stage_mem (s : A) (k : ℕ) (f : Polynomial A) :
    k2DilateSt_stage s k f ∈ k2DilateSt_pullback s := by
  rw [k2DilateSt_mem_pullback, k2DilateSt_stage_fst, k2DilateSt_stage_snd,
    k2DilateSt_evalZero_scale, Polynomial.eval_zero_map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_mem

/-- The stage map `ι_k : A[X] → P`. -/
noncomputable def k2DilateSt_toPullback (s : A) (k : ℕ) :
    Polynomial A →+* k2DilateSt_pullback s :=
  (k2DilateSt_stage s k).codRestrict (k2DilateSt_pullback s) (k2DilateSt_stage_mem s k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_toPullback

theorem k2DilateSt_coe_toPullback (s : A) (k : ℕ) (f : Polynomial A) :
    ((k2DilateSt_toPullback s k f : k2DilateSt_pullback s) :
      A × Polynomial (Localization.Away s)) = k2DilateSt_stage s k f :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_coe_toPullback

/-- **Cocone in `P`**: `ι_{k+t} ∘ μ_{s^t} = ι_k`. -/
theorem k2DilateSt_toPullback_comp_scale (s : A) (k t : ℕ) :
    (k2DilateSt_toPullback s (k + t)).comp (k2CubeDilate_scale A (s ^ t)) =
      k2DilateSt_toPullback s k :=
  RingHom.ext fun f ↦ Subtype.ext (k2DilateSt_stage_scale s k t f)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_toPullback_comp_scale

end DilateStPullback

end GroupApproximation.BooneHigman.Metabelian.ElemFP
