import GroupApproximation.Analysis.HyperlinearTraceVanishingProof
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.SoficHyperlinearTrace
import GroupApproximation.Analysis.PrintedUltrafilterHyperlinearTrace
import GroupApproximation.Analysis.TracialUltraproductCStar
import GroupApproximation.Meta.AxiomGuard

/-!
# From trace-preserving matrix models to the maximal group C⋆-algebra in the tracial ultraproduct

Lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex` at origin/main
8b36733d7, "Brown's formulation", tex 277–279 (census row `fc6e6384121b`): "So `L(G)` embeds in `𝓡^ω`
[Kirchberg, Radulescu], [Ozawa, Proposition 7.1]".

A trace-preserving unitary matrix model `S` of `G` (`Analysis/HyperlinearTraceVanishingModels`) and a
free ultrafilter `ω` give:

* `unitarySeq S g`: the models of `g`, as a bounded matrix sequence;
* `unitaryHom S ω hω : G →* unitary (∏_ω M_k)`: exact in the tracial ultraproduct, because the
  multiplicativity and identity defects are `‖·‖₂`-null along `atTop`, hence along `ω`;
* `ultratraceCLM_unitaryHom_of_ne_one`: `tr_ω (u_g) = 0` for `g ≠ 1`;
* `exists_maximalGroupCStar_hom`: the universal property of `C*(G)` gives a `⋆`-homomorphism
  `π : C*(G) → ∏_ω M_k` with `π(u_g)` the class of the models of `g`, and `tr_ω ∘ π` equal to the
  canonical trace of `C*(G)`.

The extension from `C*(G)` to `L(G)` is the next module's work.
-/

namespace GroupApproximation
namespace OzawaEmbedding

open Filter Matrix TracialUltraproduct ShulmanTrace HyperlinearTraceVanishing
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] (S : TracePreservingMatrixModel G) [∀ n, Nonempty (S.model n)]

/-- Each model of a group element has operator norm `1`. -/
theorem norm_modelMatrix (n : ℕ) (g : G) :
    ‖((S.map n g : Matrix.unitaryGroup (S.model n) ℂ) : Matrix (S.model n) (S.model n) ℂ)‖ = 1 := by
  haveI : Nontrivial (Matrix (S.model n) (S.model n) ℂ) := by
    refine nontrivial_of_ne 1 0 fun h ↦ ?_
    have h1 : ‖(1 : Matrix (S.model n) (S.model n) ℂ)‖ = 1 := norm_one
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  exact CStarRing.norm_of_mem_unitary (S.map n g).2

/-- The models of `g`, as a bounded matrix sequence. -/
def unitarySeq (g : G) : ModelBoundedSequence (fun n ↦ S.model n) :=
  boundedSeqOfBound
    (fun n ↦ ((S.map n g : Matrix.unitaryGroup (S.model n) ℂ) : Matrix (S.model n) (S.model n) ℂ))
    (fun n ↦ le_of_eq (norm_modelMatrix S n g))

@[simp] theorem unitarySeq_apply (g : G) (n : ℕ) :
    unitarySeq S g n =
      ((S.map n g : Matrix.unitaryGroup (S.model n) ℂ) : Matrix (S.model n) (S.model n) ℂ) :=
  rfl

omit [∀ n, Nonempty (S.model n)] in
/-- The model of `1` is as close to `1` as the defect at `(1, 1)`. -/
theorem hsDistSq_map_one (n : ℕ) :
    hsDistSq (S.model n) ((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) 1 =
      hsDistSq (S.model n) ((S.map n (1 * 1) : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ)
        (((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) *
          ((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ)) := by
  rw [mul_one]
  have hinv := hsDistSq_mul_left_of_unitary (S.map n 1).2 (S.modelNonempty n)
    ((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) 1
  rw [mul_one] at hinv
  rw [← hinv, hsDistSq_symm]

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hω in
/-- **The multiplicativity defect is `‖·‖₂`-null along `ω`.** -/
theorem isHilbertSchmidtNull_unitarySeq_mul (g h : G) :
    IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
      (unitarySeq S (g * h) - unitarySeq S g * unitarySeq S h) := by
  rw [isHilbertSchmidtNull_iff_sq]
  have hkey : ∀ n, hsNormSq (S.model n)
      ((unitarySeq S (g * h) - unitarySeq S g * unitarySeq S h) n) =
        hsDistSq (S.model n) ((S.map n (g * h) : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ)
          (((S.map n g : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) *
            ((S.map n h : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ)) := by
    intro n
    rw [modelSeq_sub_apply, modelSeq_mul_apply, unitarySeq_apply, unitarySeq_apply,
      unitarySeq_apply]
    rfl
  have hlim : Tendsto (fun n ↦ hsDistSq (S.model n)
      ((S.map n (g * h) : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ)
      (((S.map n g : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) *
        ((S.map n h : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ))) atTop (nhds 0) := by
    refine tendsto_zero_of_forall_eventually_lt (fun n ↦ ?_) fun ε hε ↦ ?_
    · rw [← hkey n]
      exact hsNormSq_nonneg _ _
    · obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h (ε / 2) (by positivity)
      exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by linarith [hN n hn]⟩
  exact (hlim.congr fun n ↦ (hkey n).symm).mono_left (coe_ultrafilter_le_atTop ω hω)

include hω in
/-- **The identity defect is `‖·‖₂`-null along `ω`.** -/
theorem isHilbertSchmidtNull_unitarySeq_one :
    IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S 1 - 1) := by
  rw [isHilbertSchmidtNull_iff_sq]
  have hkey : ∀ n, hsNormSq (S.model n) ((unitarySeq S 1 - 1) n) =
      hsDistSq (S.model n) ((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) 1 := by
    intro n
    rw [modelSeq_sub_apply, modelSeq_one_apply, unitarySeq_apply]
    rfl
  have hlim : Tendsto (fun n ↦ hsDistSq (S.model n)
      ((S.map n 1 : Matrix.unitaryGroup (S.model n) ℂ) : Matrix _ _ ℂ) 1) atTop (nhds 0) := by
    refine tendsto_zero_of_forall_eventually_lt (fun n ↦ ?_) fun ε hε ↦ ?_
    · rw [← hkey n]
      exact hsNormSq_nonneg _ _
    · obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative 1 1 (ε / 2) (by positivity)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
      rw [hsDistSq_map_one S n]
      linarith [hN n hn]
  exact (hlim.congr fun n ↦ (hkey n).symm).mono_left (coe_ultrafilter_le_atTop ω hω)

/-- The class of the models of `g` is unitary: each coordinate is exactly unitary. -/
theorem mk_unitarySeq_mem_unitary (g : G) :
    tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S g) ∈
      unitary (TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) := by
  rw [Unitary.mem_iff, tracialMatrixQuotient_star_mk, ← map_mul, ← map_mul]
  constructor
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (star (unitarySeq S g) * unitarySeq S g - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply, modelSeq_one_apply,
        unitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff'.mp (S.map n g).2
      rw [hu, sub_self]
    rw [mk_eq_mk_of_isHilbertSchmidtNull hnull, map_one]
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) (ω : Filter ℕ)
        (unitarySeq S g * star (unitarySeq S g) - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply, modelSeq_one_apply,
        unitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff.mp (S.map n g).2
      rw [hu, sub_self]
    rw [mk_eq_mk_of_isHilbertSchmidtNull hnull, map_one]

/-- **The models induce a unitary representation in the tracial ultraproduct.** -/
def unitaryHom : G →* unitary (TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) where
  toFun g := ⟨tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S g),
    mk_unitarySeq_mem_unitary S ω g⟩
  map_one' := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S 1) = 1
    rw [mk_eq_mk_of_isHilbertSchmidtNull (isHilbertSchmidtNull_unitarySeq_one S ω hω), map_one]
  map_mul' g h := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S (g * h)) =
      tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S g) *
        tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S h)
    rw [← map_mul]
    exact mk_eq_mk_of_isHilbertSchmidtNull (isHilbertSchmidtNull_unitarySeq_mul S ω hω g h)

theorem coe_unitaryHom (g : G) :
    ((unitaryHom S ω hω g : unitary (TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))) :
        TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) =
      tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S g) :=
  rfl

/-- **The ultratrace vanishes on the nontrivial group elements.** -/
theorem ultratraceCLM_unitaryHom_of_ne_one {g : G} (hg : g ≠ 1) :
    ultratraceCLM (fun n ↦ S.model n) ω
        ((unitaryHom S ω hω g : unitary (TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))) :
          TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ)) = 0 := by
  rw [coe_unitaryHom, ultratraceCLM_apply, ultratrace_mk]
  refine tendsto_nhds_unique (tendsto_seqUltratrace (fun n ↦ S.model n) ω (unitarySeq S g)) ?_
  exact (S.trace_tendsto_ne g hg).mono_left (coe_ultrafilter_le_atTop ω hω)

include hω in
/-- **The maximal group C⋆-algebra maps to the tracial ultraproduct**, sending `u_g` to the class of
the models of `g`, with `tr_ω ∘ π` the canonical trace. -/
theorem exists_maximalGroupCStar_hom :
    ∃ π : MaximalGroupCStar G →⋆ₐ[ℂ] TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ),
      (∀ g : G, π (maximalGroupCStarGenerator G g) =
        tracialMatrixQuotientMk (fun n ↦ S.model n) (ω : Filter ℕ) (unitarySeq S g)) ∧
        ∀ a : MaximalGroupCStar G,
          ultratraceCLM (fun n ↦ S.model n) ω (π a) = canonicalMaximalTrace G a := by
  obtain ⟨π, hπgen, hπtrace⟩ := canonicalMaximalTrace_factorsThrough G (unitaryHom S ω hω)
    (ultratraceCLM (fun n ↦ S.model n) ω) (ultratraceCLM_one (fun n ↦ S.model n) ω)
    (fun g hg ↦ ultratraceCLM_unitaryHom_of_ne_one S ω hω hg)
  exact ⟨π, hπgen, fun a ↦ DFunLike.congr_fun hπtrace a⟩

end

end OzawaEmbedding
end GroupApproximation

#audit_axioms GroupApproximation.OzawaEmbedding.exists_maximalGroupCStar_hom
