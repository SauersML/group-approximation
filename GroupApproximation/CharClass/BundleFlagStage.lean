import GroupApproximation.CharClass.BundleFlag

/-!
# Complex vector bundles in the projection model, XXVIII: one stage of the flag
tower

`BundleFlag` builds the tower and identifies its first stage, `Fl₁(p) = P(p)`,
but says nothing about the higher ones.  A per-stage Leray-Hirsch iteration
needs each stage to be the projective bundle of something over the stage below.

That something is the **rest bundle**: the pullback of `p` minus the lines
already chosen.  It is a projection because the sum of the lines is one and is
absorbed by the pullback, and its rank is `n` less.  A point of `Fl_{n+1}(p)` is
then a point of `Fl_n(p)` together with a line orthogonal to the ones chosen so
far, which is exactly a point of `P(flagRest p n)`.

`flagOne` is the case `n = 0` up to `flagRest p 0` being the pullback of `p`
along the constant map; it is not re-derived here.

## Main declarations

* `flagRest` — the rest bundle, with `trace_flagRest` and `rank_flagRest`.
* `flagSucc` — `Fl_{n+1}(p) ≃ₜ P(flagRest p n)`, over `Fl_n(p)`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section FlagStage

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-! ### The rest bundle -/

/-- **The rest bundle**: the pullback of `p` minus the lines already chosen. -/
noncomputable def flagRest (p : Bundle X ι) (n : ℕ) : Bundle (Flag p n) ι where
  toFun w := comap (flagProj p n) p w - ∑ l ∈ Finset.range n, flagLine p n l w
  continuous_toFun :=
    (comap (flagProj p n) p).continuous.sub
      (continuous_finsetSum _ fun l _ => (flagLine p n l).continuous)
  isStarProjection_toFun w :=
    isStarProjection_sub ((comap (flagProj p n) p).isStarProjection w)
      (flagSum_isStarProjection p n w) (p_mul_flagSum p n w) (flagSum_mul_p p n w)

theorem flagRest_apply (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    flagRest p n w
      = comap (flagProj p n) p w - ∑ l ∈ Finset.range n, flagLine p n l w := rfl

theorem trace_flagRest (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    (flagRest p n w).trace = (p (flagProj p n w)).trace - (n : ℂ) := by
  rw [flagRest_apply, Matrix.trace_sub, trace_flagSum]
  rfl

/-- **The rest bundle has rank `n` less.** -/
theorem rank_flagRest (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    (flagRest p n).rank w + n = p.rank (flagProj p n w) := by
  have h : (((flagRest p n).rank w : ℕ) : ℂ)
      = ((p.rank (flagProj p n w) : ℕ) : ℂ) - (n : ℂ) := by
    rw [← trace_eq_rank, trace_flagRest, trace_eq_rank]
  have h2 : (((flagRest p n).rank w + n : ℕ) : ℂ) = ((p.rank (flagProj p n w) : ℕ) : ℂ) := by
    push_cast
    rw [h]
    ring
  exact_mod_cast h2

/-- Each chosen line is orthogonal to the rest. -/
theorem flagLine_mul_flagSum (p : Bundle X ι) (n : ℕ) (w : Flag p n) {k : ℕ}
    (hk : k ∈ Finset.range n) :
    flagLine p n k w * (∑ l ∈ Finset.range n, flagLine p n l w) = flagLine p n k w := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · exact (flagLine p n k).mul_self w
  · intro l hl hlk
    exact flagLine_mul_flagLine p (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)
      (Ne.symm hlk) w
  · intro h
    exact absurd hk h

theorem flagLine_mul_flagRest (p : Bundle X ι) {n k : ℕ} (hk : k < n) (w : Flag p n) :
    flagLine p n k w * flagRest p n w = 0 := by
  rw [flagRest_apply, Matrix.mul_sub, flagLine_mul_comap p hk w,
    flagLine_mul_flagSum p n w (Finset.mem_range.mpr hk), sub_self]

theorem flagRest_mul_flagLine (p : Bundle X ι) {n k : ℕ} (hk : k < n) (w : Flag p n) :
    flagRest p n w * flagLine p n k w = 0 := by
  rw [flagRest_apply, Matrix.sub_mul, comap_mul_flagLine p hk w,
    flagSum_mul_flagLine p n w (Finset.mem_range.mpr hk), sub_self]

/-! ### The stage identification -/

theorem flagForget_snd (p : Bundle X ι) (n : ℕ) (w : Flag p (n + 1)) (k : ℕ) :
    ((flagForget p n w : Flag p n) : X × (ℕ → Matrix ι ι ℂ)).2 k
      = if k < n then (w : X × (ℕ → Matrix ι ι ℂ)).2 k else 0 := rfl


theorem flagLine_flagForget (p : Bundle X ι) (n : ℕ) {l : ℕ} (hl : l < n)
    (w : Flag p (n + 1)) :
    flagLine p n l (flagForget p n w) = flagLine p (n + 1) l w := by
  show (if l < n then (w : X × (ℕ → Matrix ι ι ℂ)).2 l else 0)
      = (w : X × (ℕ → Matrix ι ι ℂ)).2 l
  rw [if_pos hl]

theorem flagRest_flagForget (p : Bundle X ι) (n : ℕ) (w : Flag p (n + 1)) :
    flagRest p n (flagForget p n w)
      = comap (flagProj p (n + 1)) p w - ∑ l ∈ Finset.range n, flagLine p (n + 1) l w := by
  rw [flagRest_apply]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  exact flagLine_flagForget p n (Finset.mem_range.mp hl) w

theorem flagSucc_toFun_mem (p : Bundle X ι) (n : ℕ) (w : Flag p (n + 1)) :
    ((flagForget p n w, (w : X × (ℕ → Matrix ι ι ℂ)).2 n)
      : Flag p n × Matrix ι ι ℂ) ∈ projSet (flagRest p n) := by
  have hn : n < n + 1 := Nat.lt_succ_self n
  refine ⟨(w.2.1 n hn).1, (w.2.1 n hn).2.1, (w.2.1 n hn).2.2.1, ?_⟩
  rw [flagRest_flagForget, Matrix.sub_mul]
  have h1 : comap (flagProj p (n + 1)) p w * (w : X × (ℕ → Matrix ι ι ℂ)).2 n
      = (w : X × (ℕ → Matrix ι ι ℂ)).2 n := (w.2.1 n hn).2.2.2
  have h2 : (∑ l ∈ Finset.range n, flagLine p (n + 1) l w)
      * (w : X × (ℕ → Matrix ι ι ℂ)).2 n = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun l hl => ?_
    exact w.2.2.1 l n (Nat.lt_succ_of_lt (Finset.mem_range.mp hl)) hn
      (Nat.ne_of_lt (Finset.mem_range.mp hl))
  rw [h1, h2, sub_zero]

theorem flagSucc_invFun_mem (p : Bundle X ι) (n : ℕ) (z : Proj (flagRest p n)) :
    (((z : Flag p n × Matrix ι ι ℂ).1 : X × (ℕ → Matrix ι ι ℂ)).1,
      fun k => if k < n then ((z : Flag p n × Matrix ι ι ℂ).1
          : X × (ℕ → Matrix ι ι ℂ)).2 k
        else if k = n then (z : Flag p n × Matrix ι ι ℂ).2 else 0)
      ∈ flagSet p (n + 1) := by
  set w := (z : Flag p n × Matrix ι ι ℂ).1 with hw
  set r := (z : Flag p n × Matrix ι ι ℂ).2 with hr
  have hrest : flagRest p n w * r = r := z.2.2.2.2
  have hpr : comap (flagProj p n) p w * r = r := by
    have hsum : (∑ l ∈ Finset.range n, flagLine p n l w) * r = 0 := by
      rw [← hrest, ← Matrix.mul_assoc, flagRest_apply, Matrix.mul_sub,
        flagSum_mul_p p n w, (flagSum_isStarProjection p n w).isIdempotentElem.eq,
        sub_self, Matrix.zero_mul]
    have := congrArg (fun M => M * r) (flagRest_apply p n w)
    simp only [Matrix.sub_mul] at this
    rw [hrest, hsum, sub_zero] at this
    exact this.symm
  have hline : ∀ k, k < n → flagLine p n k w * r = 0 := by
    intro k hk
    rw [← hrest, ← Matrix.mul_assoc, flagLine_mul_flagRest p hk w, Matrix.zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    by_cases h : k < n
    · simp only [if_pos h]
      exact w.2.1 k h
    · have hkn : k = n := by omega
      simp only [if_neg h, if_pos hkn]
      exact ⟨z.2.1, z.2.2.1, z.2.2.2.1, hkn ▸ hpr⟩
  · intro k l hk hl hkl
    by_cases hkn : k < n
    · by_cases hln : l < n
      · simp only [if_pos hkn, if_pos hln]
        exact w.2.2.1 k l hkn hln hkl
      · have : l = n := by omega
        simp only [if_pos hkn, if_neg hln, if_pos this]
        exact hline k hkn
    · have hk' : k = n := by omega
      have hln : l < n := by omega
      simp only [if_neg hkn, if_pos hk', if_pos hln]
      have hL : (flagLine p n l w)ᴴ = flagLine p n l w := (w.2.1 l hln).1
      have hR : ((z : Flag p n × Matrix ι ι ℂ).2)ᴴ = (z : Flag p n × Matrix ι ι ℂ).2 := z.2.1
      have h := congrArg Matrix.conjTranspose (hline l hln)
      rwa [Matrix.conjTranspose_mul, hL, hR, Matrix.conjTranspose_zero] at h
  · intro k hk
    have h1 : ¬ k < n := by omega
    have h2 : ¬ k = n := by omega
    simp only [if_neg h1, if_neg h2]

/-- **One stage of the flag tower.**  A point of `Fl_{n+1}(p)` is a point of
`Fl_n(p)` together with a line orthogonal to the ones already chosen. -/
noncomputable def flagSucc (p : Bundle X ι) (n : ℕ) :
    Flag p (n + 1) ≃ₜ Proj (flagRest p n) where
  toFun w := ⟨(flagForget p n w, (w : X × (ℕ → Matrix ι ι ℂ)).2 n),
    flagSucc_toFun_mem p n w⟩
  invFun z := ⟨(((z : Flag p n × Matrix ι ι ℂ).1 : X × (ℕ → Matrix ι ι ℂ)).1,
      fun k => if k < n then ((z : Flag p n × Matrix ι ι ℂ).1
          : X × (ℕ → Matrix ι ι ℂ)).2 k
        else if k = n then (z : Flag p n × Matrix ι ι ℂ).2 else 0),
    flagSucc_invFun_mem p n z⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext k
    by_cases h : k < n
    · simp only [if_pos h, flagForget_snd]
    · by_cases h2 : k = n
      · subst h2
        simp
      · simp only [if_neg h, if_neg h2]
        exact (w.2.2.2 k (by omega)).symm
  right_inv z := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      funext k
      simp only [flagForget_snd]
      by_cases h : k < n
      · simp only [if_pos h]
      · simp only [if_neg h]
        exact ((z : Flag p n × Matrix ι ι ℂ).1.2.2.2 k (by omega)).symm
    · simp
  continuous_toFun :=
    (((flagForget p n).continuous).prodMk
      (((continuous_apply n).comp continuous_snd).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine ((continuous_fst.comp continuous_subtype_val).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk (continuous_pi fun k => ?_)
    by_cases h : k < n
    · simp only [if_pos h]
      exact ((continuous_apply k).comp (continuous_snd.comp continuous_subtype_val)).comp
        (continuous_fst.comp continuous_subtype_val)
    · by_cases h2 : k = n
      · simp only [if_neg h, if_pos h2]
        exact continuous_snd.comp continuous_subtype_val
      · simp only [if_neg h, if_neg h2]
        exact continuous_const

/-- **The stage identification is over the stage below**, by `rfl`. -/
theorem flagSucc_over_base (p : Bundle X ι) (n : ℕ) (w : Flag p (n + 1)) :
    projPi (flagRest p n) (flagSucc p n w) = flagForget p n w := rfl

end FlagStage

end Bundle

end CharClass
end GroupApproximation
