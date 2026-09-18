import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Every point of the pullback comes from a stage

Lane `bh-met-90s`, lifting module.  Notation as in `ElemFPK2DilateStRing`.

`k2DilateSt_lifts_of_mem`: every `q = (a, h) ∈ P = A ×_L L[X]` is `ι_k f` for some `k` and
`f ∈ A[X]` (denominator clearing).  Write `h = C(h(0)) + X h'` with `h(0) = λ a`.  Then
`(a, C(λ a)) = ι_0 (C a)`, and `(0, X h')` is a sum of products of the points `(0, c X)`,
`c ∈ L`.  With `c = λ(b) u^n` (`IsLocalization.Away.surj`), `(0, c X) = ι_n (C b · X)`.  The
image of the stages is closed under `+` and `·`, because
`ι_k f ∘ ι_l g = ι_{k+l} (μ_{s^l} f ∘ μ_{s^k} g)` for `∘ ∈ {+, ·}` (cocone relation).

`k2DilateSt_liftStage`, `k2DilateSt_liftPoly`: a chosen such pair `(k, f)` for each `q ∈ P`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section DilateStLift

variable {A : Type*} [CommRing A]

/-- `q` is the image of some stage. -/
abbrev k2DilateSt_Lifts (s : A) (q : A × Polynomial (Localization.Away s)) : Prop :=
  ∃ (k : ℕ) (f : Polynomial A), k2DilateSt_stage s k f = q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_Lifts

theorem k2DilateSt_lifts_add {s : A} {q q' : A × Polynomial (Localization.Away s)}
    (hq : k2DilateSt_Lifts s q) (hq' : k2DilateSt_Lifts s q') : k2DilateSt_Lifts s (q + q') := by
  obtain ⟨k, f, rfl⟩ := hq
  obtain ⟨l, g, rfl⟩ := hq'
  refine ⟨k + l, k2CubeDilate_scale A (s ^ l) f + k2CubeDilate_scale A (s ^ k) g, ?_⟩
  rw [map_add, k2DilateSt_stage_scale, add_comm k l, k2DilateSt_stage_scale]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_add

theorem k2DilateSt_lifts_mul {s : A} {q q' : A × Polynomial (Localization.Away s)}
    (hq : k2DilateSt_Lifts s q) (hq' : k2DilateSt_Lifts s q') : k2DilateSt_Lifts s (q * q') := by
  obtain ⟨k, f, rfl⟩ := hq
  obtain ⟨l, g, rfl⟩ := hq'
  refine ⟨k + l, k2CubeDilate_scale A (s ^ l) f * k2CubeDilate_scale A (s ^ k) g, ?_⟩
  rw [map_mul, k2DilateSt_stage_scale, add_comm k l, k2DilateSt_stage_scale]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_mul

theorem k2DilateSt_lifts_C (s : A) (a : A) :
    k2DilateSt_Lifts s (a, Polynomial.C (algebraMap A (Localization.Away s) a)) :=
  ⟨0, Polynomial.C a, k2DilateSt_stage_C s 0 a⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_C

/-- `(0, c X)` lifts: with `c λ(s)^n = λ(b)`, it is `ι_n (C b · X)`. -/
theorem k2DilateSt_lifts_C_mul_X (s : A) (c : Localization.Away s) :
    k2DilateSt_Lifts s (0, Polynomial.C c * Polynomial.X) := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj s c
  refine ⟨n, Polynomial.C b * Polynomial.X, ?_⟩
  rw [map_mul, k2DilateSt_stage_C, k2DilateSt_stage_X, Prod.mk_mul_mk, mul_zero, ← mul_assoc,
    ← Polynomial.C_mul, ← hb, mul_assoc c (algebraMap A _ s ^ n) (k2DilateSt_inv s ^ n),
    ← mul_pow, k2DilateSt_mul_inv, one_pow, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_C_mul_X

theorem k2DilateSt_lifts_C_mul_X_pow (s : A) (c : Localization.Away s) (n : ℕ) :
    k2DilateSt_Lifts s (0, Polynomial.C c * Polynomial.X ^ (n + 1)) := by
  induction n with
  | zero =>
      rw [zero_add, pow_one]
      exact k2DilateSt_lifts_C_mul_X s c
  | succ n ih =>
      have e : ((0 : A), Polynomial.C c * Polynomial.X ^ (n + 1 + 1)) =
          (0, Polynomial.C c * Polynomial.X ^ (n + 1)) * (0, Polynomial.C 1 * Polynomial.X) := by
        rw [Prod.mk_mul_mk, mul_zero, Polynomial.C_1, one_mul, pow_succ _ (n + 1), mul_assoc]
      rw [e]
      exact k2DilateSt_lifts_mul ih (k2DilateSt_lifts_C_mul_X s 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_C_mul_X_pow

/-- `(0, X h)` lifts for every `h ∈ L[X]`. -/
theorem k2DilateSt_lifts_X_mul (s : A) (h : Polynomial (Localization.Away s)) :
    k2DilateSt_Lifts s (0, Polynomial.X * h) := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq =>
      have e : ((0 : A), Polynomial.X * (p + q)) = (0, Polynomial.X * p) + (0, Polynomial.X * q) :=
        by rw [Prod.mk_add_mk, add_zero, mul_add]
      rw [e]
      exact k2DilateSt_lifts_add hp hq
  | monomial n c =>
      have e : Polynomial.X * Polynomial.monomial n c =
          Polynomial.C c * Polynomial.X ^ (n + 1) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        ring
      rw [e]
      exact k2DilateSt_lifts_C_mul_X_pow s c n

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_X_mul

/-- **Every point of the pullback lifts to a stage.** -/
theorem k2DilateSt_lifts_of_mem {s : A} {q : A × Polynomial (Localization.Away s)}
    (hq : q ∈ k2DilateSt_pullback s) : k2DilateSt_Lifts s q := by
  obtain ⟨a, h⟩ := q
  have hq' : algebraMap A (Localization.Away s) a = h.eval 0 := hq
  have e : ((a, h) : A × Polynomial (Localization.Away s)) =
      (a, Polynomial.C (algebraMap A (Localization.Away s) a)) + (0, Polynomial.X * h.divX) := by
    rw [Prod.mk_add_mk, add_zero, hq', ← Polynomial.coeff_zero_eq_eval_zero, add_comm,
      Polynomial.X_mul_divX_add]
  rw [e]
  exact k2DilateSt_lifts_add (k2DilateSt_lifts_C s a) (k2DilateSt_lifts_X_mul s _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_lifts_of_mem

theorem k2DilateSt_exists_stage_eq (s : A) (q : k2DilateSt_pullback s) :
    ∃ (k : ℕ) (f : Polynomial A),
      k2DilateSt_stage s k f = (q : A × Polynomial (Localization.Away s)) :=
  k2DilateSt_lifts_of_mem q.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_exists_stage_eq

/-- A chosen stage for `q ∈ P`. -/
noncomputable def k2DilateSt_liftStage (s : A) (q : k2DilateSt_pullback s) : ℕ :=
  (k2DilateSt_exists_stage_eq s q).choose

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_liftStage

/-- A chosen lift of `q ∈ P` at the stage `k2DilateSt_liftStage s q`. -/
noncomputable def k2DilateSt_liftPoly (s : A) (q : k2DilateSt_pullback s) : Polynomial A :=
  (k2DilateSt_exists_stage_eq s q).choose_spec.choose

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_liftPoly

theorem k2DilateSt_stage_lift (s : A) (q : k2DilateSt_pullback s) :
    k2DilateSt_stage s (k2DilateSt_liftStage s q) (k2DilateSt_liftPoly s q) =
      (q : A × Polynomial (Localization.Away s)) :=
  (k2DilateSt_exists_stage_eq s q).choose_spec.choose_spec

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_stage_lift

end DilateStLift

end GroupApproximation.BooneHigman.Metabelian.ElemFP
