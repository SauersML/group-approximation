import GroupApproximation.Analysis.LIXConnectingMap
import GroupApproximation.Analysis.LIXSimplicity

set_option autoImplicit false

/-!
# Fullness of the connecting maps of the STW LIX tower

The manuscript's §5: for `0 ≠ a ∈ A_k`, choose `i ≥ k` with `π_{k,i}(x_i)` in the open set
where `a` does not vanish; then `φ_{k,i}(a)(x_i) ≠ 0`, so the point-evaluation summand of
`φ_i` makes `φ_{k,i+1}(a)` nonzero in *every* fibre of `X_{i+1}`, and a section nonzero in
every fibre is full.

Two things are sharper here than in the manuscript.

* **No positivity is used.**  The manuscript takes `a ≥ 0` so that its fibre values have
  nonzero trace.  Instead we run the argument on `aᴴ a`, whose trace at `w` is
  `∑_{s,t} |a(w)_{st}|²`; it is nonzero exactly when `a(w) ≠ 0`
  (`STW59.eq_zero_of_trace_conjTranspose_mul_self`).  So `cs-simplicity`'s `0 ≤ a`
  hypothesis is spare.
* **Fullness comes out exactly, with no ε.**  The matrix units of the ambient homogeneous
  algebra are global, so `∑_{s,t} (E_{st} compressed) X (E_{ts} compressed) = Tr(X) • E`
  is an identity, not an approximation, and `Tr(X)` is invertible in `C(X_i, ℂ)` because it
  is a nowhere-zero continuous function on a compact space.  `LIX.isFull_of_sum_eq_one`
  then applies directly.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix Kronecker ComplexOrder CStarAlgebra

noncomputable section


/-! ### Two lemmas that do not see the rank

Both are stated for an arbitrary index type, so they are shared by every rank and stay
outside `Gen`.  They are placed before it because `Gen.sum_single_conj` consumes
`sum_single_diag`. -/

/-- `∑_s E_{ss} c = c • 1`. -/
theorem sum_single_diag {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R] (c : R) :
    (∑ s : ι, Matrix.single s s c) = c • (1 : Matrix ι ι R) := by
  classical
  refine Matrix.ext fun a b => ?_
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a, Matrix.single_apply_same, if_pos rfl, smul_eq_mul, mul_one]
    · intro s _ hs
      exact Matrix.single_apply_of_ne _ _ _ _ _ (fun hc => hs hc.1)
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  · rw [if_neg h, smul_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    refine Matrix.single_apply_of_ne _ _ _ _ _ (fun hc => h ?_)
    rw [← hc.1, ← hc.2]

set_option maxHeartbeats 1000000 in
/-- `ofFunctionMatrix` commutes with finite sums. -/
theorem ofFunctionMatrix_sum {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {κ : Type*} (s : Finset κ) (f : κ → Matrix ι ι C(X, ℂ)) :
    ofFunctionMatrix (∑ k ∈ s, f k) = ∑ k ∈ s, ofFunctionMatrix (f k) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ofFunctionMatrix_zero
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, ofFunctionMatrix_add, ih]

namespace Gen

variable (n : ℕ)

/-! ### The compression is injective on the corner -/

/-- On the corner, `sᴴ M(x_i) s` vanishes only if `M(x_i)` does: `s sᴴ` is the fibre unit,
so `M(x_i) = s (sᴴ M(x_i) s) sᴴ`. -/
theorem compressMat_eq_zero_iff (i : ℕ) {M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)}
    (hM : Eproj n i * M * Eproj n i = M) :
    compressMat n i M = 0 ↔ matEval (stagePoint n i) M = 0 := by
  constructor
  · intro h
    have hmem : matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M
        * matEval (stagePoint n i) (Eproj n i) = matEval (stagePoint n i) M := by
      rw [← matEval_mul, ← matEval_mul, hM]
    rw [← stageFrame_mul_conjTranspose] at hmem
    have hre : stageFrame n i * (stageFrame n i)ᴴ * matEval (stagePoint n i) M
          * (stageFrame n i * (stageFrame n i)ᴴ)
        = stageFrame n i * compressMat n i M * (stageFrame n i)ᴴ := by
      show stageFrame n i * (stageFrame n i)ᴴ * matEval (stagePoint n i) M
          * (stageFrame n i * (stageFrame n i)ᴴ)
        = stageFrame n i * ((stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i)
          * (stageFrame n i)ᴴ
      simp only [Matrix.mul_assoc]
    rw [hre, h, Matrix.mul_zero, Matrix.zero_mul] at hmem
    exact hmem.symm
  · intro h
    show (stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i = 0
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

/-! ### Half one: the twisted summand is nonzero in every fibre -/

/-- The `(1,1)` block of `φ_i(a)` at `w` is `a` at `π_i(w)`; this is `rfl`. -/
theorem stageEval_connect_inl (i : ℕ) (w : baseX n (i + 1)) (a : StageAlgebra n i)
    (s t : EIdx n i) :
    stageEval n (i + 1) w (connect n i a) (eIdxSucc n i (Sum.inl s)) (eIdxSucc n i (Sum.inl t))
      = stageEval n i (baseProj n i w) a s t := by
  rcases s with s | s <;> rcases t with t | t <;> rfl

/-- **`φ_i` reflects nonvanishing along `π_i`**: this is what carries "nonzero somewhere"
up the tower. -/
theorem stageEval_connect_ne_zero_of_pull (i : ℕ) (w : baseX n (i + 1)) {a : StageAlgebra n i}
    (h : stageEval n i (baseProj n i w) a ≠ 0) : stageEval n (i + 1) w (connect n i a) ≠ 0 := by
  intro hzero
  refine h (Matrix.ext fun s t => ?_)
  have hst := congrFun (congrFun hzero (eIdxSucc n i (Sum.inl s))) (eIdxSucc n i (Sum.inl t))
  rw [Matrix.zero_apply] at hst
  rw [Matrix.zero_apply, ← stageEval_connect_inl n i w a s t]
  exact hst

/-- **Half one.**  If `b` does not vanish in the fibre over the stage point `x_i`, then
`φ_i(b)` vanishes in no fibre at all: its new block at `w` is
`(sᴴ b(x_i) s) ⊗ taut(w)`, the first factor is nonzero by `compressMat_eq_zero_iff` and the
second is a rank-one projection. -/
theorem stageEval_connect_ne_zero (i : ℕ) {b : StageAlgebra n i}
    (hb : stageEval n i (stagePoint n i) b ≠ 0) (w : baseX n (i + 1)) :
    stageEval n (i + 1) w (connect n i b) ≠ 0 := by
  have hCne : compressMat n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))) ≠ 0 := by
    intro h
    exact hb ((compressMat_eq_zero_iff n i (toFunctionMatrix_mem_corner b)).mp h)
  have hLne : matEval w (newLine n i) ≠ 0 := by
    intro h
    have ht : (matEval w (newLine n i)).trace = 1 := by
      rw [trace_matEval, trace_newLine]
      rfl
    rw [h, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  obtain ⟨c, d, hcd⟩ : ∃ c d,
      compressMat n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))) c d ≠ 0 := by
    by_contra hcon
    refine hCne (Matrix.ext fun c d => ?_)
    rw [Matrix.zero_apply]
    by_contra hcd
    exact hcon ⟨c, d, hcd⟩
  obtain ⟨p, q, hpq⟩ : ∃ p q, matEval w (newLine n i) p q ≠ 0 := by
    by_contra hcon
    refine hLne (Matrix.ext fun p q => ?_)
    rw [Matrix.zero_apply]
    by_contra hpq
    exact hcon ⟨p, q, hpq⟩
  intro hzero
  have hentry := congrFun (congrFun hzero (eIdxSucc n i (Sum.inr (c, p))))
    (eIdxSucc n i (Sum.inr (d, q)))
  rw [Matrix.zero_apply] at hentry
  refine (mul_ne_zero hcd hpq) ?_
  rw [← hentry]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The matrix-unit averaging.**  For `X` in the corner of `E_j`,
`∑_{s,t} (E_j E_{st} E_j) X (E_j E_{ts} E_j) = Tr(X) • E_j`.

The matrix units of the ambient homogeneous algebra are global, which is exactly why the
corner of a projection over a compact base has no room for a proper ideal that meets every
fibre. -/
theorem sum_single_conj (j : ℕ) (X : Matrix (EIdx n j) (EIdx n j) C(baseX n j, ℂ))
    (hX : Eproj n j * X * Eproj n j = X) :
    (∑ s : EIdx n j, ∑ t : EIdx n j,
        (Eproj n j * Matrix.single s t 1 * Eproj n j) * X
          * (Eproj n j * Matrix.single t s 1 * Eproj n j))
      = Matrix.trace X • Eproj n j := by
  have hP : Eproj n j * Eproj n j = Eproj n j := (isStarProjection_Eproj n j).isIdempotentElem.eq
  have hterm : ∀ s t : EIdx n j,
      (Eproj n j * Matrix.single s t 1 * Eproj n j) * X
        * (Eproj n j * Matrix.single t s 1 * Eproj n j)
      = Eproj n j * Matrix.single s s (X t t) * Eproj n j := by
    intro s t
    have hre : (Eproj n j * Matrix.single s t 1 * Eproj n j) * X
          * (Eproj n j * Matrix.single t s 1 * Eproj n j)
        = Eproj n j * (Matrix.single s t 1 * (Eproj n j * X * Eproj n j) * Matrix.single t s 1)
          * Eproj n j := by
      simp only [Matrix.mul_assoc]
    rw [hre, hX, Matrix.single_mul_mul_single, one_mul, mul_one]
  have hinner : ∀ s : EIdx n j,
      (∑ t : EIdx n j, Eproj n j * Matrix.single s s (X t t) * Eproj n j)
        = Eproj n j * Matrix.single s s (Matrix.trace X) * Eproj n j := by
    intro s
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 2
    refine Matrix.ext fun a b => ?_
    rw [Matrix.sum_apply]
    by_cases h : s = a ∧ s = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same]
      rfl
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ h]
      exact Finset.sum_eq_zero fun t _ => Matrix.single_apply_of_ne _ _ _ _ _ h
  rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => hterm s t,
    Finset.sum_congr rfl fun s _ => hinner s, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_single_diag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]

end Gen

/-! ### The `n = 2` instance -/

/-- On the corner, `sᴴ M(x_i) s` vanishes only if `M(x_i)` does. -/
theorem compressMat_eq_zero_iff (i : ℕ) {M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hM : Eproj i * M * Eproj i = M) :
    compressMat i M = 0 ↔ matEval (stagePoint i) M = 0 :=
  Gen.compressMat_eq_zero_iff 2 i hM

/-- The `(1,1)` block of `φ_i(a)` at `w` is `a` at `π_i(w)`. -/
theorem stageEval_connect_inl (i : ℕ) (w : baseX (i + 1)) (a : StageAlgebra i)
    (s t : EIdx i) :
    stageEval (i + 1) w (connect i a) (eIdxSucc i (Sum.inl s)) (eIdxSucc i (Sum.inl t))
      = stageEval i (baseProj i w) a s t :=
  Gen.stageEval_connect_inl 2 i w a s t

/-- **`φ_i` reflects nonvanishing along `π_i`.** -/
theorem stageEval_connect_ne_zero_of_pull (i : ℕ) (w : baseX (i + 1)) {a : StageAlgebra i}
    (h : stageEval i (baseProj i w) a ≠ 0) : stageEval (i + 1) w (connect i a) ≠ 0 :=
  Gen.stageEval_connect_ne_zero_of_pull 2 i w h

/-- **Half one.**  If `b` does not vanish in the fibre over the stage point `x_i`, then
`φ_i(b)` vanishes in no fibre at all. -/
theorem stageEval_connect_ne_zero (i : ℕ) {b : StageAlgebra i}
    (hb : stageEval i (stagePoint i) b ≠ 0) (w : baseX (i + 1)) :
    stageEval (i + 1) w (connect i b) ≠ 0 :=
  Gen.stageEval_connect_ne_zero 2 i hb w

/-- **The matrix-unit averaging.**  For `X` in the corner of `E_j`,
`∑_{s,t} (E_j E_{st} E_j) X (E_j E_{ts} E_j) = Tr(X) • E_j`. -/
theorem sum_single_conj (j : ℕ) (X : Matrix (EIdx j) (EIdx j) C(baseX j, ℂ))
    (hX : Eproj j * X * Eproj j = X) :
    (∑ s : EIdx j, ∑ t : EIdx j,
        (Eproj j * Matrix.single s t 1 * Eproj j) * X
          * (Eproj j * Matrix.single t s 1 * Eproj j))
      = Matrix.trace X • Eproj j :=
  Gen.sum_single_conj 2 j X hX

/-! ### What remains

The last step, that a section vanishing in no fibre is full, is the matrix-unit averaging
of `sum_single_conj` applied to `X := aᴴ a`, whose trace is nowhere zero and therefore
invertible in `C(X_j, ℂ)`; scaling the left coefficients by that inverse turns the
averaging into an exact `∑ x_l * a * y_l = 1`, which `LIX.isFull_of_sum_eq_one` consumes.
It is in `Analysis/LIXConnectingMapFullnessSum.lean` rather than here, green, because the
assembly elaborates slowly and should not hold this module back.
-/

end

end STW59
end GroupApproximation
