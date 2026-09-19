/-! ## Unital ⋆-homomorphisms as completely positive linear maps -/

section StarAlgHomLinear

variable {A : Type*} {B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A unital ⋆-homomorphism, as a linear map, is completely positive. -/
theorem isCompletelyPositive_starAlgHom_toLinear (π : A →⋆ₐ[ℂ] B) :
    IsCompletelyPositive (π.toNonUnitalStarAlgHom : A →ₗ[ℂ] B) :=
  isCompletelyPositive_of_starAlgHom π.toNonUnitalStarAlgHom

theorem starAlgHom_toLinear_one (π : A →⋆ₐ[ℂ] B) :
    (π.toNonUnitalStarAlgHom : A →ₗ[ℂ] B) 1 = 1 :=
  map_one π

end StarAlgHomLinear

/-! ## Approximate models on a finite set of generators -/

section Approximation

variable {G : Type} [Group G]

/-- **One step of the diagonal argument** (row A2, tex l.54–59).  Under the LLP, a trace-preserving
matrix model gives, for every finite `F ⊆ G` and `ε > 0`, a unital completely positive matrix model
of `C⋆(G)` whose multiplicative defects on pairs of generators over `F`, and whose trace errors on
generators over `F`, are below `ε`. -/
theorem exists_approximateModel
    (hLLP : HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G))
    (M : TracePreservingMatrixModel G) (F : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (_ : Nonempty Y)
      (φ : MaximalGroupCStar G →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ g ∈ F, ∀ h ∈ F, hsNorm Y
          (φ (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
            - φ (maximalGroupCStarGenerator G g)
              * φ (maximalGroupCStarGenerator G h)) < ε) ∧
      ∀ g ∈ F, ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
          - normTrace Y (φ (maximalGroupCStarGenerator G g))‖ < ε := by
  classical
  haveI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  obtain ⟨π, hπ⟩ := exists_modelLift M
  have hEsys : IsOperatorSystem (generatorSystem (generatorSet F)) :=
    isOperatorSystem_generatorSystem (one_mem_generatorSet F)
      (fun g hg ↦ inv_mem_generatorSet hg)
  have hsurj : Function.Surjective (tracialMatrixQuotientQuotient M.model atTop) :=
    fun c ↦ (tracialMatrixQuotientMk_surjective M.model atTop c).imp fun b hb ↦
      (tracialMatrixQuotientQuotient_apply M.model atTop b).trans hb
  have hπcp := isCompletelyPositive_starAlgHom_toLinear π
  have hπ1 := starAlgHom_toLinear_one π
  obtain ⟨ψ, hψcp, hψ1, hψlift⟩ :=
    hLLP (ModelBoundedSequence M.model) (TracialMatrixQuotient M.model atTop)
      (tracialMatrixQuotientQuotient M.model atTop) hsurj _ hπcp hπ1
      (generatorSystem (generatorSet F)) hEsys inferInstance
  have hq : ∀ x : generatorSystem (generatorSet F),
      tracialMatrixQuotientMk M.model atTop (ψ x) = π x := fun x ↦ hψlift x
  -- the Arveson extensions of the coordinates
  have hext : ∀ n : ℕ, ∃ Ψ : MaximalGroupCStar G →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card (M.model n))) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card (M.model n)))),
      IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧
        ∀ x : generatorSystem (generatorSet F),
          Ψ (x : MaximalGroupCStar G) = euclideanize (M.model n) ((ψ x) n) := by
    intro n
    have hcp' := isCompletelyPositiveOn_comp_starAlgHom hψcp
      (euclideanCoordinateStarAlgHom (X := M.model) n)
    obtain ⟨Ψ, hΨcp, hΨ1, hΨext⟩ :=
      A2OperatorSystems.exists_ucp_extension_of_system' hEsys _ hcp'
        (fun x hx ↦ by
          show euclideanCoordinateStarAlgHom (X := M.model) n (ψ x) = 1
          rw [hψ1 x hx, map_one])
    exact ⟨Ψ, hΨcp, hΨ1, fun x ↦ hΨext x⟩
  choose Ψ hΨcp hΨ1 hΨext using hext
  have hφu : ∀ (n : ℕ) (g : G) (hg : g ∈ generatorSet F),
      (matrixOfEuclidean (M.model n)).comp (Ψ n) (maximalGroupCStarGenerator G g)
        = (ψ ⟨maximalGroupCStarGenerator G g, generator_mem_generatorSystem hg⟩) n :=
    fun n g hg ↦
      (congrArg (fun T ↦ matrixOfEuclidean (M.model n) T)
        (hΨext n ⟨maximalGroupCStarGenerator G g, generator_mem_generatorSystem hg⟩)).trans
        (matrixOfEuclidean_euclideanize (M.model n) _)
  -- the multiplicative defects are null
  have hmulnull : ∀ (g : G) (hg : g ∈ F) (h : G) (hh : h ∈ F),
      IsHilbertSchmidtNull M.model atTop
        (ψ ⟨maximalGroupCStarGenerator G (g * h),
            generator_mem_generatorSystem (mul_mem_generatorSet hg hh)⟩
          - ψ ⟨maximalGroupCStarGenerator G g,
              generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
            * ψ ⟨maximalGroupCStarGenerator G h,
              generator_mem_generatorSystem (mem_generatorSet_of_mem hh)⟩) := by
    intro g hg h hh
    rw [← tracialMatrixQuotientMk_eq_zero_iff, map_sub, map_mul, hq, hq, hq]
    show π (maximalGroupCStarGenerator G (g * h))
        - π (maximalGroupCStarGenerator G g) * π (maximalGroupCStarGenerator G h) = 0
    rw [← map_mul π, maximalGroupCStarGenerator_mul, sub_self]
  -- the lift is close to the model at each generator
  have htrnull : ∀ (g : G) (hg : g ∈ F),
      IsHilbertSchmidtNull M.model atTop
        (ψ ⟨maximalGroupCStarGenerator G g,
            generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
          - modelUnitarySeq M g) := by
    intro g hg
    rw [← tracialMatrixQuotientMk_eq_zero_iff, map_sub, hq]
    show π (maximalGroupCStarGenerator G g)
        - tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M g) = 0
    rw [hπ g, sub_self]
  have hevmul : ∀ᶠ n in atTop, ∀ g ∈ F, ∀ h ∈ F, hsNorm (M.model n)
      ((matrixOfEuclidean (M.model n)).comp (Ψ n)
          (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
        - (matrixOfEuclidean (M.model n)).comp (Ψ n) (maximalGroupCStarGenerator G g)
          * (matrixOfEuclidean (M.model n)).comp (Ψ n)
            (maximalGroupCStarGenerator G h)) < ε := by
    refine (Filter.eventually_all_finset F).mpr fun g hg ↦ ?_
    refine (Filter.eventually_all_finset F).mpr fun h hh ↦ ?_
    filter_upwards [eventually_lt_of_tendsto_zero (hmulnull g hg h hh) hε] with n hn
    rw [maximalGroupCStarGenerator_mul, hφu n (g * h) (mul_mem_generatorSet hg hh),
      hφu n g (mem_generatorSet_of_mem hg), hφu n h (mem_generatorSet_of_mem hh)]
    exact hn
  have hevtr : ∀ᶠ n in atTop, ∀ g ∈ F,
      ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
        - normTrace (M.model n)
          ((matrixOfEuclidean (M.model n)).comp (Ψ n)
            (maximalGroupCStarGenerator G g))‖ < ε := by
    refine (Filter.eventually_all_finset F).mpr fun g hg ↦ ?_
    have hz : Tendsto (fun n ↦ normTrace (M.model n)
        ((ψ ⟨maximalGroupCStarGenerator G g,
            generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
          - modelUnitarySeq M g) n)) atTop (nhds 0) :=
      squeeze_zero_norm (fun n ↦ norm_normTrace_le_hsNorm (M.model n)
        ((ψ ⟨maximalGroupCStarGenerator G g,
            generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
          - modelUnitarySeq M g) n)) (htrnull g hg)
    have htr : Tendsto (fun n ↦ normTrace (M.model n)
        (M.map n g : Matrix (M.model n) (M.model n) ℂ)) atTop
        (nhds (canonicalMaximalTrace G (maximalGroupCStarGenerator G g))) := by
      by_cases hg1 : g = 1
      · rw [hg1, canonicalMaximalTrace_generator_one]
        exact M.trace_tendsto_one
      · rw [canonicalMaximalTrace_generator_of_ne_one G hg1]
        exact M.trace_tendsto_ne g hg1
    have hsum := htr.add hz
    rw [add_zero] at hsum
    have hsum' : Tendsto (fun n ↦ normTrace (M.model n)
        ((matrixOfEuclidean (M.model n)).comp (Ψ n)
          (maximalGroupCStarGenerator G g))) atTop
        (nhds (canonicalMaximalTrace G (maximalGroupCStarGenerator G g))) := by
      refine hsum.congr fun n ↦ ?_
      show normTrace (M.model n) (M.map n g : Matrix (M.model n) (M.model n) ℂ)
          + normTrace (M.model n)
            ((ψ ⟨maximalGroupCStarGenerator G g,
                generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
              - modelUnitarySeq M g) n)
        = normTrace (M.model n)
            ((matrixOfEuclidean (M.model n)).comp (Ψ n) (maximalGroupCStarGenerator G g))
      rw [hφu n g (mem_generatorSet_of_mem hg), modelSeq_sub_apply, normTrace_sub,
        modelUnitarySeq_apply]
      ring
    filter_upwards [Metric.tendsto_nhds.mp hsum' ε hε] with n hn
    rw [dist_eq_norm, norm_sub_rev] at hn
    exact hn
  obtain ⟨n, hn1, hn2⟩ := (hevmul.and hevtr).exists
  exact ⟨M.model n, inferInstance, (matrixOfEuclidean (M.model n)).comp (Ψ n),
    by rw [LinearMap.comp_apply, hΨ1 n, matrixOfEuclidean_one],
    isCompletelyPositiveOnMatrices_matrixOfEuclidean (M.model n) (Ψ n) (hΨcp n),
    hn1, hn2⟩

end Approximation

/-! ## The theorems -/

/-- **The local lifting property and a trace-preserving matrix model give the factorization
property** (Ozawa, preprint p. 24; row A2, tex l.54–59): local ucp lifts on generator operator
systems, Arveson extension, a diagonal choice, and the dense-generator upgrade to an amenable trace
model. -/
theorem localLiftingFactorization (G : Type) [Group G] [Countable G]
    (hLLP : HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G))
    (hM : HasTracePreservingMatrixModel G) :
    NinetyNineProblems.HasFactorizationProperty G := by
  classical
  obtain ⟨M⟩ := hM
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat G
  have hstep : ∀ k : ℕ, ∃ (Y : FiniteModel) (_ : Nonempty Y)
      (φ : MaximalGroupCStar G →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ g ∈ (Finset.range (k + 1)).image e, ∀ h ∈ (Finset.range (k + 1)).image e,
        hsNorm Y
          (φ (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
            - φ (maximalGroupCStarGenerator G g)
              * φ (maximalGroupCStarGenerator G h)) < 1 / ((k : ℝ) + 1)) ∧
      ∀ g ∈ (Finset.range (k + 1)).image e,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
          - normTrace Y (φ (maximalGroupCStarGenerator G g))‖ < 1 / ((k : ℝ) + 1) :=
    fun k ↦ exists_approximateModel hLLP M ((Finset.range (k + 1)).image e)
      (by positivity)
  choose Y hY φ hone hcp hmul htr using hstep
  haveI : ∀ k, Nonempty (Y k) := hY
  have hcontr : ∀ k a, ‖φ k a‖ ≤ ‖a‖ := fun k a ↦ ucp_norm_le (φ k) (hone k) (hcp k) a
  have hmem : ∀ g : G, ∀ᶠ k in atTop, g ∈ (Finset.range (k + 1)).image e := by
    intro g
    obtain ⟨i, rfl⟩ := he g
    exact Filter.eventually_atTop.mpr
      ⟨i, fun k hk ↦ Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩⟩
  have hsmall : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmulgen : ∀ a ∈ Set.range (maximalGroupCStarGenerator G),
      ∀ b ∈ Set.range (maximalGroupCStarGenerator G),
        Tendsto (fun k ↦ hsNorm (Y k) (φ k (a * b) - φ k a * φ k b)) atTop (nhds 0) := by
    rintro a ⟨g, rfl⟩ b ⟨h, rfl⟩
    refine squeeze_zero' (Filter.Eventually.of_forall fun k ↦ hsNorm_nonneg _ _) ?_ hsmall
    filter_upwards [hmem g, hmem h] with k hgk hhk
    exact (hmul k g hgk h hhk).le
  have htrgen : ∀ a ∈ Set.range (maximalGroupCStarGenerator G),
      Tendsto (fun k ↦ ‖canonicalMaximalTrace G a - normTrace (Y k) (φ k a)‖)
        atTop (nhds 0) := by
    rintro a ⟨g, rfl⟩
    refine squeeze_zero' (Filter.Eventually.of_forall fun k ↦ norm_nonneg _) ?_ hsmall
    filter_upwards [hmem g] with k hgk
    exact (htr k g hgk).le
  exact Nonempty.intro (amenableTraceModel_of_dense_generators φ hone hcp hcontr
    (canonicalMaximalTrace G) (Set.range (maximalGroupCStarGenerator G))
    (maximalGroupCStar_dense_span_generator G) hmulgen htrgen)

/-- **No factorization property, no local lifting property** (Ozawa, §7; row A2, tex l.54–59): a
countable hyperlinear group without the factorization property has a full C⋆-algebra without the
local lifting property. -/
theorem not_hasLocalLiftingProperty_of_not_hasFactorizationProperty
    (G : Type) [Group G] [Countable G] (hH : IsHyperlinear G)
    (hF : ¬ NinetyNineProblems.HasFactorizationProperty G) :
    ¬ HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G) := fun hLLP ↦
  hF (localLiftingFactorization G hLLP (hasTracePreservingMatrixModel_of_isHyperlinear G hH))

end

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_closed_axioms exists_approximateModel
#audit_closed_axioms localLiftingFactorization
#audit_closed_axioms not_hasLocalLiftingProperty_of_not_hasFactorizationProperty
