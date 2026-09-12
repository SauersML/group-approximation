import GroupApproximation.CharClass.BundlePairs
import GroupApproximation.CharClass.BundleInvariance

/-!
# Complex vector bundles in the projection model, XI: the flag bundle

The geometry of the splitting principle.  Over the projective bundle `P(p)` the
tautological line `L₁` sits inside the pullback `π^* p`, and its complement

    flagComplement p = π^* p - L₁

is again a bundle, of rank one less.  Iterating that construction is the flag
bundle, and on it the pullback of `p` splits as a sum of rank-one projections.

## The tower, without dependent types

Iterating `P(-)` literally produces a tower whose base space changes at every
stage, so a `Nat`-indexed tower of spaces is a `Type`-valued recursion and every
statement about it carries its own `TopologicalSpace` instance.  The same object
has a description with a **single ambient space**, and that is what is built
here: a point of the `n`-th stage is a point of `X` together with an orthogonal
`n`-tuple of lines inside the fibre,

    flagSet p n = {(x, q) | q k is a rank-one subprojection of p x for k < n,
                            the q k are pairwise orthogonal,
                            q k = 0 for k ≥ n}

which lives in `X × (ℕ → Matrix ι ι ℂ)` for every `n` at once.  The forgetful
maps `flagSet p (n+1) → flagSet p n` are the tower's projections, `flagOne`
identifies the first stage with `P(p)`, and each coordinate `q k` is a
continuous rank-one projection-valued map, i.e. a line bundle, **by
construction**: no choice, no local triviality and no induction is needed to
produce the lines.

What does need a proof is that at the top stage the lines exhaust the bundle,
`flag_decomposition`.  That is the trace argument: the sum of the lines is a
subprojection of `p` of the same trace, and a projection of trace zero is zero.

Injectivity of the pullback on cohomology is **not** proved here; that is
Leray-Hirsch, and it belongs to `cc-projective`.  This file supplies the spaces,
the projections and the orthogonal decomposition.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### One step: the complement of the tautological line -/

section Complement

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

theorem p_mul_tautLine (p : Bundle X ι) (z : Proj p) :
    p ((projPi p) z) * tautLine p z = tautLine p z := absorb_of_mem_projSet z.2

theorem tautLine_mul_p (p : Bundle X ι) (z : Proj p) :
    tautLine p z * p ((projPi p) z) = tautLine p z := absorb_right_of_mem_projSet z.2

/-- **The complement of the tautological line** inside the pullback of `p`.  Its
rank is one less than the rank of `p` (`rank_flagComplement`). -/
noncomputable def flagComplement (p : Bundle X ι) : Bundle (Proj p) ι where
  toFun z := p ((projPi p) z) - tautLine p z
  continuous_toFun :=
    (p.continuous.comp (projPi p).continuous).sub (tautLine p).continuous
  isStarProjection_toFun z :=
    isStarProjection_sub (p.isStarProjection _) ((tautLine p).isStarProjection z)
      (p_mul_tautLine p z) (tautLine_mul_p p z)

@[simp]
theorem flagComplement_apply (p : Bundle X ι) (z : Proj p) :
    flagComplement p z = p ((projPi p) z) - tautLine p z := rfl

/-- The tautological line and its complement add up to the pullback. -/
theorem tautLine_add_flagComplement (p : Bundle X ι) (z : Proj p) :
    tautLine p z + flagComplement p z = comap (projPi p) p z := by
  rw [flagComplement_apply]
  show tautLine p z + (p ((projPi p) z) - tautLine p z) = p ((projPi p) z)
  abel

theorem tautLine_mul_flagComplement (p : Bundle X ι) (z : Proj p) :
    tautLine p z * flagComplement p z = 0 := by
  rw [flagComplement_apply, Matrix.mul_sub, tautLine_mul_p p z, (tautLine p).mul_self z,
    sub_self]

theorem flagComplement_mul_tautLine (p : Bundle X ι) (z : Proj p) :
    flagComplement p z * tautLine p z = 0 := by
  rw [flagComplement_apply, Matrix.sub_mul, p_mul_tautLine p z, (tautLine p).mul_self z,
    sub_self]

theorem trace_flagComplement (p : Bundle X ι) (z : Proj p) :
    (flagComplement p z).trace = (p ((projPi p) z)).trace - 1 := by
  rw [flagComplement_apply, Matrix.trace_sub, trace_tautLine]

/-- **The complement has rank one less.** -/
theorem rank_flagComplement (p : Bundle X ι) (z : Proj p) :
    (flagComplement p).rank z + 1 = p.rank ((projPi p) z) := by
  have h : (((flagComplement p).rank z : ℕ) : ℂ) + 1 = ((p.rank ((projPi p) z) : ℕ) : ℂ) := by
    rw [← trace_eq_rank, ← trace_eq_rank, trace_flagComplement]
    ring
  exact_mod_cast h

end Complement

/-! ### The flag bundle -/

section Flag

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **The `n`-th stage of the flag bundle**: a point of the base together with
an orthogonal `n`-tuple of lines in its fibre. -/
def flagSet (p : Bundle X ι) (n : ℕ) : Set (X × (ℕ → Matrix ι ι ℂ)) :=
  {w | (∀ k, k < n → w.2 k ∈ projFibreSet (p w.1))
     ∧ (∀ k l, k < n → l < n → k ≠ l → w.2 k * w.2 l = 0)
     ∧ (∀ k, n ≤ k → w.2 k = 0)}

/-- The `n`-th stage of the flag bundle as a space. -/
abbrev Flag (p : Bundle X ι) (n : ℕ) : Type := ↥(flagSet p n)

theorem mem_flagSet_iff {p : Bundle X ι} {n : ℕ} {w : X × (ℕ → Matrix ι ι ℂ)} :
    w ∈ flagSet p n ↔
      (∀ k, k < n → w.2 k ∈ projFibreSet (p w.1))
     ∧ (∀ k l, k < n → l < n → k ≠ l → w.2 k * w.2 l = 0)
     ∧ (∀ k, n ≤ k → w.2 k = 0) := Iff.rfl

/-- The projection of the flag bundle to the base. -/
def flagProj (p : Bundle X ι) (n : ℕ) : C(Flag p n, X) :=
  ⟨fun w => (w : X × (ℕ → Matrix ι ι ℂ)).1, continuous_fst.comp continuous_subtype_val⟩

@[simp]
theorem flagProj_apply (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    flagProj p n w = (w : X × (ℕ → Matrix ι ι ℂ)).1 := rfl

/-- **The `k`-th tautological line of the flag bundle.**  It is a rank-one
projection-valued map by construction: the point *is* its tuple of lines. -/
def flagLine (p : Bundle X ι) (n k : ℕ) : Bundle (Flag p n) ι where
  toFun w := (w : X × (ℕ → Matrix ι ι ℂ)).2 k
  continuous_toFun :=
    ((continuous_apply k).comp continuous_snd).comp continuous_subtype_val
  isStarProjection_toFun w := by
    by_cases h : k < n
    · exact isStarProjection_matrix_iff.mpr ⟨(w.2.1 k h).1, (w.2.1 k h).2.1⟩
    · rw [w.2.2.2 k (not_lt.mp h)]
      exact IsStarProjection.zero _

@[simp]
theorem flagLine_apply (p : Bundle X ι) (n k : ℕ) (w : Flag p n) :
    flagLine p n k w = (w : X × (ℕ → Matrix ι ι ℂ)).2 k := rfl

theorem trace_flagLine (p : Bundle X ι) {n k : ℕ} (hk : k < n) (w : Flag p n) :
    (flagLine p n k w).trace = 1 := (w.2.1 k hk).2.2.1

theorem flagLine_mul_flagLine (p : Bundle X ι) {n k l : ℕ} (hk : k < n) (hl : l < n)
    (hkl : k ≠ l) (w : Flag p n) : flagLine p n k w * flagLine p n l w = 0 :=
  w.2.2.1 k l hk hl hkl

/-- Each line sits inside the pullback of `p`. -/
theorem comap_mul_flagLine (p : Bundle X ι) {n k : ℕ} (hk : k < n) (w : Flag p n) :
    comap (flagProj p n) p w * flagLine p n k w = flagLine p n k w := (w.2.1 k hk).2.2.2

theorem flagLine_mul_comap (p : Bundle X ι) {n k : ℕ} (hk : k < n) (w : Flag p n) :
    flagLine p n k w * comap (flagProj p n) p w = flagLine p n k w := by
  show (w : X × (ℕ → Matrix ι ι ℂ)).2 k * p (w : X × (ℕ → Matrix ι ι ℂ)).1
      = (w : X × (ℕ → Matrix ι ι ℂ)).2 k
  have h := congrArg Matrix.conjTranspose (w.2.1 k hk).2.2.2
  rwa [Matrix.conjTranspose_mul, (w.2.1 k hk).1, p.conjTranspose_eq] at h

/-- The forgetful map of the tower, `Fl_{n+1}(p) → Fl_n(p)`: drop the last
line. -/
def flagForget (p : Bundle X ι) (n : ℕ) : C(Flag p (n + 1), Flag p n) where
  toFun w := ⟨((w : X × (ℕ → Matrix ι ι ℂ)).1,
      fun k => if k < n then (w : X × (ℕ → Matrix ι ι ℂ)).2 k else 0), by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [if_pos hk]
      exact w.2.1 k (Nat.lt_succ_of_lt hk)
    · intro k l hk hl hkl
      simp only [if_pos hk, if_pos hl]
      exact w.2.2.1 k l (Nat.lt_succ_of_lt hk) (Nat.lt_succ_of_lt hl) hkl
    · intro k hk
      simp only [if_neg (Nat.not_lt.mpr hk)]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_fst.comp continuous_subtype_val).prodMk (continuous_pi fun k => ?_)
    by_cases h : k < n
    · simp only [if_pos h]
      exact ((continuous_apply k).comp continuous_snd).comp continuous_subtype_val
    · simp only [if_neg h]
      exact continuous_const

theorem flagProj_comp_flagForget (p : Bundle X ι) (n : ℕ) :
    (flagProj p n).comp (flagForget p n) = flagProj p (n + 1) := rfl

/-! ### The first stage is the projective bundle -/

/-- **`Fl₁(p) = P(p)`**: a one-flag is a point of the projective bundle. -/
def flagOne (p : Bundle X ι) : Flag p 1 ≃ₜ Proj p where
  toFun w := ⟨((w : X × (ℕ → Matrix ι ι ℂ)).1, (w : X × (ℕ → Matrix ι ι ℂ)).2 0),
    w.2.1 0 Nat.one_pos⟩
  invFun z := ⟨((z : X × Matrix ι ι ℂ).1,
      fun k => if k = 0 then (z : X × Matrix ι ι ℂ).2 else 0), by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst hk0
      show (if (0 : ℕ) = 0 then (z : X × Matrix ι ι ℂ).2 else 0)
        ∈ projFibreSet (p (z : X × Matrix ι ι ℂ).1)
      rw [if_pos rfl]
      exact z.2
    · intro k l hk hl hkl
      have hkl' : k = l := by omega
      exact absurd hkl' hkl
    · intro k hk
      have hk0 : ¬ k = 0 := by omega
      exact if_neg hk0⟩
  left_inv w := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext k
    by_cases h : k = 0
    · subst h
      simp
    · simp only [if_neg h]
      exact (w.2.2.2 k (by omega)).symm
  right_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    simp
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (((continuous_apply 0).comp continuous_snd).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_fst.comp continuous_subtype_val).prodMk (continuous_pi fun k => ?_)
    by_cases h : k = 0
    · simp only [if_pos h]
      exact continuous_snd.comp continuous_subtype_val
    · simp only [if_neg h]
      exact continuous_const

theorem flagProj_flagOne (p : Bundle X ι) (w : Flag p 1) :
    projPi p (flagOne p w) = flagProj p 1 w := rfl

/-! ### The decomposition at the top stage -/

theorem flagSum_mul_flagLine (p : Bundle X ι) (n : ℕ) (w : Flag p n) {k : ℕ}
    (hk : k ∈ Finset.range n) :
    (∑ l ∈ Finset.range n, flagLine p n l w) * flagLine p n k w = flagLine p n k w := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · exact (flagLine p n k).mul_self w
  · intro l hl hlk
    exact flagLine_mul_flagLine p (Finset.mem_range.mp hl) (Finset.mem_range.mp hk) hlk w
  · intro h
    exact absurd hk h

theorem flagSum_isStarProjection (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    IsStarProjection (∑ l ∈ Finset.range n, flagLine p n l w) := by
  refine isStarProjection_matrix_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    exact (w.2.1 l (Finset.mem_range.mp hl)).1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    exact flagSum_mul_flagLine p n w hl

theorem trace_flagSum (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    (∑ l ∈ Finset.range n, flagLine p n l w).trace = (n : ℂ) := by
  rw [Matrix.trace_sum]
  rw [Finset.sum_congr rfl fun l hl => trace_flagLine p (Finset.mem_range.mp hl) w]
  simp

theorem p_mul_flagSum (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    comap (flagProj p n) p w * (∑ l ∈ Finset.range n, flagLine p n l w)
      = ∑ l ∈ Finset.range n, flagLine p n l w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  exact comap_mul_flagLine p (Finset.mem_range.mp hl) w

theorem flagSum_mul_p (p : Bundle X ι) (n : ℕ) (w : Flag p n) :
    (∑ l ∈ Finset.range n, flagLine p n l w) * comap (flagProj p n) p w
      = ∑ l ∈ Finset.range n, flagLine p n l w := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  exact flagLine_mul_comap p (Finset.mem_range.mp hl) w

/-- **The splitting principle, geometric half.**  On the top stage of the flag
bundle the pullback of `p` is the sum of the `r` tautological lines, which are
pairwise orthogonal rank-one projections.  This is the equality of
projection-valued maps that Whitney's formula and the parity computation
consume. -/
theorem flag_decomposition (p : Bundle X ι) (r : ℕ) (hr : ∀ x, (p x).trace = (r : ℂ))
    (w : Flag p r) :
    comap (flagProj p r) p w = ∑ l ∈ Finset.range r, flagLine p r l w := by
  have hsub : IsStarProjection
      (comap (flagProj p r) p w - ∑ l ∈ Finset.range r, flagLine p r l w) :=
    isStarProjection_sub ((comap (flagProj p r) p).isStarProjection w)
      (flagSum_isStarProjection p r w) (p_mul_flagSum p r w) (flagSum_mul_p p r w)
  have htr : (comap (flagProj p r) p w - ∑ l ∈ Finset.range r, flagLine p r l w).trace = 0 := by
    rw [Matrix.trace_sub, trace_flagSum]
    show (p (flagProj p r w)).trace - (r : ℂ) = 0
    rw [hr]
    ring
  exact sub_eq_zero.mp (proj_eq_zero_of_trace_eq_zero hsub htr)

end Flag

end Bundle

end CharClass
end GroupApproximation
