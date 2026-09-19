import GroupApproximation.Sofic.WeakMFUltraproduct
import GroupApproximation.Sofic.WeakMFTransfer
import GroupApproximation.Sofic.HyperlinearNonScalar

/-!
# Regular-trace operator-norm models of LEF groups

An arbitrary weak-MF approximation need not remember the regular group trace.
This file constructs a stronger approximation for every countable LEF group.
The matrices are the left-regular permutation matrices of the finite local
models.  Consequently distinct fixed group elements have relative normalized
trace exactly zero at every sufficiently late stage.

This is the trace input needed by the faithful symmetric-amalgam argument.  It
is proved here directly from local finite models; no C*-algebraic amalgamation
or literature theorem is assumed.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- A sequential weak-MF approximation carrying the regular group trace.
For distinct `g,h`, the normalized trace of `u_g u_h*` is eventually exactly
zero, rather than merely bounded away from one. -/
structure RegularTraceWeakMFApproximation (G : Type u) [Group G]
    extends WeakMFApproximation G where
  regularTraceEventually : ∀ g h : G, g ≠ h → ∃ N, ∀ n ≥ N,
    normTrace (model n)
      ((map n g : Matrix (model n) (model n) ℂ) *
        (map n h : Matrix (model n) (model n) ℂ)ᴴ) = 0

namespace RegularTraceWeakMFApproximation

/-- Forgetting the trace certificate leaves an ordinary weak-MF
approximation. -/
abbrev toWeakMF (A : RegularTraceWeakMFApproximation G) :
    WeakMFApproximation G := A.toWeakMFApproximation

/-- The trace-enhanced approximation still gives the canonical faithful
operator-norm ultraproduct representation. -/
theorem exists_normUltraproductEmbedding
    (A : RegularTraceWeakMFApproximation G) {U : Ultrafilter ℕ}
    (hcof : (U : Filter ℕ) ≤ Filter.cofinite) :
    ∃ ρ : G →* UniversalWeakMF U A.model, Function.Injective ρ :=
  A.toWeakMF.exists_normUltraproductEmbedding hcof

/-- Filter form of the exact regular-trace certificate. -/
theorem regularTrace_eventually (A : RegularTraceWeakMFApproximation G)
    {g h : G} (hne : g ≠ h) :
    ∀ᶠ n in Filter.atTop,
      normTrace (A.model n)
        ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n h : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 := by
  obtain ⟨N, hN⟩ := A.regularTraceEventually g h hne
  exact Filter.eventually_atTop.2 ⟨N, hN⟩

/-- Evaluate a finitely supported complex group-ring element in one matrix
stage of a regular-trace approximation. -/
noncomputable def matrixGroupRing (A : RegularTraceWeakMFApproximation G)
    (n : ℕ) : (G →₀ ℂ) →ₗ[ℂ] Matrix (A.model n) (A.model n) ℂ :=
  Finsupp.linearCombination ℂ fun g ↦
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

theorem matrixGroupRing_eq_sum (A : RegularTraceWeakMFApproximation G)
    (n : ℕ) (c : G →₀ ℂ) :
    A.matrixGroupRing n c = ∑ g ∈ c.support,
      c g • (A.map n g : Matrix (A.model n) (A.model n) ℂ) := by
  classical
  simp [matrixGroupRing, Finsupp.linearCombination_apply, Finsupp.sum]

/-- A unitary is exactly normalized-trace paired with itself by `1`. -/
theorem normTrace_map_mul_conjTranspose_self
    (A : RegularTraceWeakMFApproximation G) (n : ℕ) (g : G) :
    normTrace (A.model n)
      ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 1 := by
  have hunit : (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
      (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ = 1 := by
    have h := (A.map n g).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [hunit, normTrace, Matrix.trace_one]
  have hcard : (((Fintype.card (A.model n) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (A.modelNonempty n).ne'
  exact div_self hcard

/-- **Exact regular-character evaluation.**  Pairing a fixed algebraic
group-ring element with the matrix assigned to `g` eventually extracts
exactly its `g`-coefficient.  Thus the limiting trace on the algebraic group
ring is the canonical regular trace, not an arbitrary trace on a weak-MF
completion. -/
theorem matrixGroupRing_trace_pairing_eventually
    (A : RegularTraceWeakMFApproximation G) (c : G →₀ ℂ) (g : G) :
    ∀ᶠ n in Filter.atTop,
      normTrace (A.model n)
        (A.matrixGroupRing n c *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = c g := by
  classical
  have heach : ∀ h ∈ c.support, ∀ᶠ n in Filter.atTop,
      normTrace (A.model n)
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) =
        if h = g then 1 else 0 := by
    intro h hh
    by_cases heq : h = g
    · subst h
      filter_upwards with n
      rw [if_pos rfl, A.normTrace_map_mul_conjTranspose_self]
    · filter_upwards [A.regularTrace_eventually heq] with n hn
      rw [if_neg heq]
      exact hn
  have hall : ∀ᶠ n in Filter.atTop, ∀ h ∈ c.support,
      normTrace (A.model n)
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) =
        if h = g then 1 else 0 :=
    (c.support.eventually_all).2 heach
  filter_upwards [hall] with n hn
  rw [matrixGroupRing_eq_sum, Finset.sum_mul]
  simp_rw [Matrix.smul_mul, normTrace, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]
  have hcard : (((Fintype.card (A.model n) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (A.modelNonempty n).ne'
  have htrace : ∀ h ∈ c.support,
      Matrix.trace
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) =
        (if h = g then 1 else 0) * (Fintype.card (A.model n) : ℂ) := by
    intro h hh
    have heval := hn h hh
    rw [normTrace, div_eq_iff hcard] at heval
    exact heval
  have hsum :
      ∑ h ∈ c.support,
          c h * Matrix.trace
            ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) =
        ∑ h ∈ c.support,
          c h * ((if h = g then 1 else 0) * (Fintype.card (A.model n) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [htrace h hh]
  rw [hsum]
  by_cases hg : g ∈ c.support
  · rw [Finset.sum_eq_single g]
    · simp [hcard]
    · intro b hb hbg
      simp [hbg]
    · simp [hg]
  · have hcg : c g = 0 := Finsupp.notMem_support_iff.mp hg
    have hsumzero :
        ∑ h ∈ c.support,
            c h * ((if h = g then 1 else 0) * (Fintype.card (A.model n) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      have hne : h ≠ g := fun heq ↦ hg (heq ▸ hh)
      simp [hne]
    rw [hcg, hsumzero, zero_div]

/-- The matrix image of an element outside `Γ` is eventually trace-orthogonal
to every fixed algebraic group-ring combination supported in `Γ`.  This is
the finite-sum form of the subgroup-detection calculation used by the GNS
argument. -/
theorem matrixGroupRing_trace_orthogonal_eventually
    (A : RegularTraceWeakMFApproximation G) (Γ : Subgroup G)
    {g : G} (hg : g ∉ Γ) (c : G →₀ ℂ)
    (hc : ∀ h ∈ c.support, h ∈ Γ) :
    ∀ᶠ n in Filter.atTop,
      normTrace (A.model n)
        (A.matrixGroupRing n c *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 := by
  classical
  have heach : ∀ h ∈ c.support, ∀ᶠ n in Filter.atTop,
      normTrace (A.model n)
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 := by
    intro h hh
    exact A.regularTrace_eventually fun heq ↦ hg (heq ▸ hc h hh)
  have hall : ∀ᶠ n in Filter.atTop, ∀ h ∈ c.support,
      normTrace (A.model n)
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 :=
    (c.support.eventually_all).2 heach
  filter_upwards [hall] with n hn
  have hcard : (((Fintype.card (A.model n) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (A.modelNonempty n).ne'
  have htrace : ∀ h ∈ c.support,
      Matrix.trace
        ((A.map n h : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 := by
    intro h hh
    have hzero := hn h hh
    rw [normTrace, div_eq_zero_iff] at hzero
    exact hzero.resolve_right hcard
  rw [matrixGroupRing_eq_sum, Finset.sum_mul]
  simp_rw [Matrix.smul_mul, normTrace, Matrix.trace_sum, Matrix.trace_smul]
  have hsum : ∑ x ∈ c.support,
      c x * Matrix.trace
        ((A.map n x : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [htrace x hx, mul_zero]
  simp_rw [smul_eq_mul]
  rw [hsum]
  simp

end RegularTraceWeakMFApproximation

/-- Every countable LEF group has operator-norm matrix models carrying the
regular trace.  At stage `n`, a local embedding on the first `n` enumerated
group elements is followed by the left-regular representation of its finite
permutation target. -/
theorem exists_regularTraceWeakMFApproximation_of_isLEF [Countable G]
    (hLEF : IsLEF G) :
    Nonempty (RegularTraceWeakMFApproximation G) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, hi⟩ := he g
    refine ⟨i, fun n hn ↦ hFmono hn ?_⟩
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.self_mem_range_succ i, hi⟩)
  have hmodels : ∀ n : ℕ, ∃ (d : ℕ) (f : G → Equiv.Perm (Fin d)),
      Set.InjOn f (F n : Set G) ∧ LocalMultiplicativeOn (F n) f :=
    fun n ↦ hLEF (F n)
  choose d f hinj hmul using hmodels
  let Y : ℕ → FiniteModel := fun n ↦
    ⟨Equiv.Perm (Fin (d n)), inferInstance, inferInstance⟩
  let U : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ := fun n g ↦
    ⟨((leftRegular (f n g))⁻¹).permMatrix ℂ,
      permMatrix_mem_unitaryGroup (Y n) _⟩
  refine ⟨{
    separation := 1
    separation_pos := by norm_num
    model := Y
    modelNonempty := fun _ ↦ Fintype.card_pos
    map := U
    asymptoticallyMultiplicative := ?_
    separatedEventually := ?_
    regularTraceEventually := ?_ }⟩
  · intro g h ε hε
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    refine ⟨max Ng Nh, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n ((le_max_left _ _).trans hn)
    have hh : h ∈ F n := hNh n ((le_max_right _ _).trans hn)
    have hlocal : f n (g * h) = f n g * f n h :=
      (hmul n).map_mul g hg h hh
    have hmatrix :
        ((leftRegular (f n g))⁻¹).permMatrix ℂ *
            ((leftRegular (f n h))⁻¹).permMatrix ℂ =
          ((leftRegular (f n (g * h)))⁻¹).permMatrix ℂ := by
      rw [hlocal, leftRegular_mul, _root_.mul_inv_rev,
        Matrix.permMatrix_mul]
    change ‖((leftRegular (f n (g * h)))⁻¹).permMatrix ℂ -
      ((leftRegular (f n g))⁻¹).permMatrix ℂ *
        ((leftRegular (f n h))⁻¹).permMatrix ℂ‖ ≤ ε
    rw [hmatrix, sub_self, norm_zero]
    exact hε.le
  · intro g h hne
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    refine ⟨max Ng Nh, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n ((le_max_left _ _).trans hn)
    have hh : h ∈ F n := hNh n ((le_max_right _ _).trans hn)
    have hfne : f n g ≠ f n h := fun hcon ↦ hne (hinj n hg hh hcon)
    have hg1 : (leftRegular (f n g))⁻¹ (1 : Equiv.Perm (Fin (d n))) =
        (f n g)⁻¹ := by
      simp [leftRegular]
    have hh1 : ¬ (leftRegular (f n h))⁻¹
        (1 : Equiv.Perm (Fin (d n))) = (f n g)⁻¹ := by
      simp only [leftRegular]
      exact fun hcon ↦ hfne (inv_injective hcon).symm
    have hGent := permMatrixC_entry (Y n) (leftRegular (f n g))⁻¹
      (1 : Equiv.Perm (Fin (d n))) (f n g)⁻¹
    have hHent := permMatrixC_entry (Y n) (leftRegular (f n h))⁻¹
      (1 : Equiv.Perm (Fin (d n))) (f n g)⁻¹
    rw [if_pos hg1] at hGent
    rw [if_neg hh1] at hHent
    have hentry : Complex.normSq
        ((((leftRegular (f n g))⁻¹).permMatrix ℂ -
          ((leftRegular (f n h))⁻¹).permMatrix ℂ)
            (1 : Equiv.Perm (Fin (d n))) (f n g)⁻¹) = 1 := by
      rw [Matrix.sub_apply, hGent, hHent, sub_zero]
      simp
    have hbound := normSq_entry_le_sq_l2_opNorm (Y n)
      (((leftRegular (f n g))⁻¹).permMatrix ℂ -
        ((leftRegular (f n h))⁻¹).permMatrix ℂ)
      (1 : Equiv.Perm (Fin (d n))) (f n g)⁻¹
    rw [hentry] at hbound
    change 1 ≤ ‖((leftRegular (f n g))⁻¹).permMatrix ℂ -
      ((leftRegular (f n h))⁻¹).permMatrix ℂ‖
    nlinarith [norm_nonneg
      (((leftRegular (f n g))⁻¹).permMatrix ℂ -
        ((leftRegular (f n h))⁻¹).permMatrix ℂ)]
  · intro g h hne
    obtain ⟨Ng, hNg⟩ := hFmem g
    obtain ⟨Nh, hNh⟩ := hFmem h
    refine ⟨max Ng Nh, fun n hn ↦ ?_⟩
    have hg : g ∈ F n := hNg n ((le_max_left _ _).trans hn)
    have hh : h ∈ F n := hNh n ((le_max_right _ _).trans hn)
    have hfne : f n h ≠ f n g := fun hcon ↦ hne (hinj n hg hh hcon.symm)
    have hq : f n h * (f n g)⁻¹ ≠ 1 := by
      intro hqone
      exact hfne (mul_inv_eq_one.mp hqone)
    have hregular : leftRegular (f n h) * (leftRegular (f n g))⁻¹ =
        leftRegular (f n h * (f n g)⁻¹) := by
      ext x
      simp [leftRegular, Equiv.Perm.mul_apply]
    have hproduct :
        ((leftRegular (f n g))⁻¹).permMatrix ℂ *
            (((leftRegular (f n h))⁻¹).permMatrix ℂ)ᴴ =
          (leftRegular (f n h * (f n g)⁻¹)).permMatrix ℂ := by
      rw [permMatrixC_conjTranspose (Y n) (leftRegular (f n h))⁻¹,
        inv_inv, ← Matrix.permMatrix_mul, hregular]
    have hdistance : hammingDistance (Y n)
        (leftRegular (f n h * (f n g)⁻¹)) 1 = 1 := by
      simpa only [leftRegular, Equiv.mulLeft_one] using
        (hammingDistance_leftRegular (Y := Equiv.Perm (Fin (d n)))
          (q := f n h * (f n g)⁻¹) (r := 1) hq)
    change normTrace (Y n)
      (((leftRegular (f n g))⁻¹).permMatrix ℂ *
        (((leftRegular (f n h))⁻¹).permMatrix ℂ)ᴴ) = 0
    rw [hproduct, normTrace_permMatrix (Y n) _ Fintype.card_pos,
      hdistance]
    norm_num

/-- In particular, every countable residually finite group has a
regular-trace operator-norm approximation. -/
theorem exists_regularTraceWeakMFApproximation_of_residuallyFinite
    [Countable G] [Group.ResiduallyFinite G] :
    Nonempty (RegularTraceWeakMFApproximation G) :=
  exists_regularTraceWeakMFApproximation_of_isLEF isLEF_of_residuallyFinite

end GroupApproximation
