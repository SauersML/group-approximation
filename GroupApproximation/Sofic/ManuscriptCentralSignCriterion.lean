import GroupApproximation.Sofic.IntrinsicCompressionMFRadical
import GroupApproximation.Sofic.KazhdanSignCriterion
import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Analysis.NormMatrixCoronaUnitary

/-!
# The central-sign criterion along its printed proof

`non_mf_groups_exist.tex`, the central-sign criterion in
`\section{The central-sign obstruction}` (the central-sign argument).  Anchored on
labels: the manuscript is under concurrent revision.

The printed proof is by contradiction from a surviving corona representation,
in three named paragraphs:

* *The negative corner.*  Coordinate unitary lifts `(V_{g,n})` of `Θ`
  (the unitary-corona lifting result); the Reynolds average `p_n = ½(1 + V_{ε,n})` of the
  two-element subgroup `F = {1, ε}`; rounding its Hermitian part at `½` by
  continuous functional calculus; the complements `q_n`, nonzero along
  infinitely many coordinates; compression and polar correction, giving an
  operator-norm asymptotic representation `(W_{g,n})` on nonzero blocks with
  `‖W_{ε,n} + 1‖ → 0`.
* *Transport on the corner.*  `c` centralizes `ι(Γ)`, so `(W_{c,n})` lies in
  the asymptotic commutant; the Kazhdan transport result applied to `x_n = W_{c,n}`
  puts the conjugated sequence `(W_{d,n})`, `d = t c t⁻¹`, in the same
  commutant; hence `‖W_{u,n} - 1‖_HS → 0` for `u = [d, ι(a)]`, and squaring.
* *The contradiction.*  `ε = u²` and `W_{ε,n} → -1` are incompatible with
  Hilbert--Schmidt triviality of `ε`.

`KazhdanCompressionCore.manuscriptCentralSignCriterion`, in
`Sofic/KazhdanSignCriterion.lean`, proves the same proposition by specializing
the *general* finite-normal obstruction of `sec:conj` to `F = {1, ε}`, whose
corner engine is the finite-stage root-capture argument of
`Sofic/MarkedCompressionRootCapture.lean`.  That is a correct proof of the
right statement, and it stays exactly where it is.  It is nevertheless not the
printed route, on two counts: the manuscript proves the sign criterion
*first and directly* and only afterwards replaces `F = {1, ε}` by an arbitrary
finite normal subgroup ("The argument used the finiteness of `F = {1,ε}` only
through the Reynolds average"), and the printed engine on the corner is
the Kazhdan transport result, not root capture.

This file supplies the declaration whose *proof route* is the printed one:
`cs_01_negative_corner`, `cs_02_transport_on_the_corner`,
`cs_03_contradiction`, assembled by `cs_04_no_corona_survival` and presented
as the manuscript's own closed proposition by
`GroupApproximation.KazhdanCompressionCore.manuscriptCentralSignCriterion`.

Statement identity with the existing theorem is definitional, not textual:
both inhabit the single closed proposition
`KazhdanCompressionCore.ManuscriptCentralSignCriterion`.

Neither the corner construction nor the trace contradiction is reproved here.
Both are the existing `FiniteNormalAverageCorner` machinery, instantiated at
the two-element subgroup `F = {1, ε}` that the manuscript uses; what changes is
that the corner is driven by transport.
-/

namespace GroupApproximation
namespace CentralSignTransport

open Filter KazhdanCornerMatrices KazhdanCompressorCorner
open scoped commutatorElement Matrix.Norms.L2Operator

-- The Hilbert-space universe of the manuscript's property-`(T)` hypothesis,
-- named exactly as in `Sofic/KazhdanSignCriterion.lean` so that the closed
-- proposition below carries the same single universe parameter as the theorem
-- it is interchangeable with, and so that consumers may write `.{0}`.
universe w

/-! ## Step 1 — the negative corner -/

/-- **Step 1 (the negative corner).**  From coordinate unitary lifts of a
corona representation in which a distinguished element `f` of a finite normal
subgroup `F` stays uniformly separated from the identity, the Reynolds average
of `F` is rounded at `½`, its complement is nonzero at all late coordinates,
and the compressed polar-corrected models form an operator-norm asymptotic
representation on which the `F`-average vanishes.

For the two-element subgroup `F = {1, ε}` of the manuscript the conclusion
`∑_{x ∈ F} W_{x,n} → 0` is exactly the printed `‖W_{ε,n} + 1‖ → 0`.

This is the four-line core of
`FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing`, taken
corona-natively from the marked model rather than from an ultraproduct
representation, so that the printed order of construction is preserved. -/
theorem cs_01_negative_corner {E : Type} [Group E]
    (F : Subgroup E) [Fintype F] [F.Normal] (f : F)
    (A : MarkedOpAlmostRepresentation E (f : E)) :
    ∃ B : OpAlmostRepresentation E,
      KazhdanCornerMatrices.OpNormVanishing B (fun n ↦
        ∑ x : F, (B.map n (x : E) :
          Matrix (B.model n) (B.model n) ℂ)) := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    FiniteNormalAverageCorner.subgroupComplementProjection_eventually_ne_zero
      F f A
  have hcorner : ∀ n ≥ N₀,
      Nonempty (FiniteNormalAverageCorner.subgroupCornerModel
        A.toOpAlmostRepresentation F n) := by
    intro n hn
    exact
      FiniteNormalAverageCorner.nonempty_subgroupCornerModel_of_complement_ne_zero
        A.toOpAlmostRepresentation F n (hN₀ n hn)
  refine ⟨FiniteNormalAverageCorner.subgroupCornerAlmostRepresentation
    A.toOpAlmostRepresentation F N₀ hcorner, ?_⟩
  exact FiniteNormalAverageCorner.subgroupCornerAlmostRepresentation_sum_vanishing
    A.toOpAlmostRepresentation F N₀ hcorner

/-! ## Step 2 — transport on the corner -/

/-- **Step 2 (transport on the corner).**  The compression defect
`u = [d, ι(a)]`, `d = t c t⁻¹`, is Hilbert--Schmidt trivial in the tracial
ultraproduct attached to *every* operator-norm almost representation — in
particular to the corner of step 1.

This is the printed paragraph, and it is proved by the printed argument:
`c` centralizes `ι(Γ)`, so `(W_{c,n})` is a uniformly bounded sequence in the
asymptotic commutant of the Kazhdan image
(`KazhdanAsymptoticCommutant.map_mem_asymptoticCommutantOf`); the one-sided
compressor `t` carries it back into that commutant by Kazhdan transport
(`KazhdanAsymptoticCommutant.transport`, packaged as
`compressionGroup_transport_both`); therefore `(W_{d,n})` asymptotically
commutes with `(W_{ι(a),n})` in normalized Hilbert--Schmidt norm, which is
exactly triviality of `u`.

The existing route to the same conclusion,
`KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom`, instead
runs the finite-stage root-capture argument of
`Sofic/MarkedCompressionRootCapture.lean`.  Both are correct; only this one is
the manuscript's. -/
theorem cs_02_transport_on_the_corner {Γ E : Type} [Group Γ] [Group E]
    (C : KazhdanCompressionCore Γ E) (B : OpAlmostRepresentation E)
    {U : Ultrafilter ℕ} (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (a : Γ) :
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof ⁅C.transported, C.iota a⁆ = 1 := by
  have hg : C.t ∈ compressionGroup C.iota.range :=
    Subgroup.subset_closure C.t_mem_compressionSet
  have hres :=
    KazhdanAsymptoticCommutant.compressionCentralizerDefect_generator_eq_one_in_hyperlinearHom
      B C.iota C.kazhdan hcof hg C.c_commutes_range ⟨a, rfl⟩
  simpa [KazhdanCompressionCore.transported] using hres

/-- **Step 2, squared.**  The distinguished sign `ε = u²` is Hilbert--Schmidt
trivial in the same tracial ultraproduct.  This is the printed "and squaring
gives `‖W_{u,n}² - 1‖_HS → 0`"; in the tracial ultraproduct the squaring is
the group law, since the ultraproduct map is a homomorphism. -/
theorem cs_02_sign_killed {Γ E : Type} [Group Γ] [Group E]
    (C : KazhdanCompressionCore Γ E) (B : OpAlmostRepresentation E)
    {U : Ultrafilter ℕ} (hcof : (U : Filter ℕ) ≤ Filter.cofinite)
    (a : Γ) (z : E) (hz : z = ⁅C.transported, C.iota a⁆ ^ 2) :
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof z = 1 := by
  rw [hz, map_pow, cs_02_transport_on_the_corner C B hcof a, one_pow]

/-! ## Step 3 — the contradiction -/

/-- **Step 3 (the contradiction).**  A finite subgroup whose corner average
vanishes in operator norm, and every element of which is Hilbert--Schmidt
trivial in the tracial ultraproduct, is impossible.

The manuscript's `‖2·1‖_HS → 0` is run here in the equivalent normalized-trace
form of `FiniteNormalAverageCorner.false_of_finite_sum_vanishing_of_hsTrivial`:
the `F`-average of the normalized traces is simultaneously within `1/8` of
`|F| ≥ 1` and within `1/8` of `0`.  The passage from ultrafilter-frequent
Hilbert--Schmidt triviality to eventual triviality along a subsequence is the
manuscript's "the coordinates are scheduled", here the reindexing along
`stage`. -/
theorem cs_03_contradiction {E : Type} [Group E]
    (F : Subgroup E) [Fintype F] (B : OpAlmostRepresentation E)
    {U₀ : Ultrafilter ℕ} (hcof : (U₀ : Filter ℕ) ≤ Filter.cofinite)
    (hsum : KazhdanCornerMatrices.OpNormVanishing B (fun n ↦
      ∑ x : F, (B.map n (x : E) :
        Matrix (B.model n) (B.model n) ℂ)))
    (hkillF : ∀ x : F,
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof (x : E) = 1) :
    False := by
  classical
  let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  let rhoHS : E →* UniversalHyperlinear U₀ S.model S.modelNonempty :=
    S.toUltraproductHom hcof
  have hcloseU : ∀ x : F, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n in (U₀ : Filter ℕ),
        hsDistSq (B.model n) (B.map n (x : E)) (B.map n 1) < epsilon := by
    intro x epsilon hepsilon
    have heqRho : rhoHS (x : E) = rhoHS 1 := by
      rw [hkillF x, map_one]
    have heqMk :
        (QuotientGroup.mk (fun n ↦ S.map n (x : E)) :
          UniversalHyperlinear U₀ S.model S.modelNonempty) =
        QuotientGroup.mk (fun n ↦ S.map n 1) := by
      simpa [rhoHS] using heqRho
    have hnull :
        (fun n ↦ S.map n 1)⁻¹ * (fun n ↦ S.map n (x : E)) ∈
          nullUnitarySubgroup U₀ S.model S.modelNonempty :=
      QuotientGroup.eq.mp heqMk.symm
    filter_upwards [hnull epsilon hepsilon] with n hn
    change hsLengthSq (S.model n)
      (((S.map n 1)⁻¹ * S.map n (x : E) :
        Matrix.unitaryGroup (S.model n) ℂ)) < epsilon at hn
    rw [coe_inv_mul,
      hsLengthSq_conjTranspose_mul (S.model n) (S.map n 1).2
        (S.modelNonempty n)] at hn
    exact hn
  let eta : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have heta (n : ℕ) : 0 < eta n := by dsimp [eta]; positivity
  have hall : ∀ n : ℕ, ∀ᶠ i in (U₀ : Filter ℕ),
      n ≤ i ∧ ∀ x : F,
        hsDistSq (B.model i) (B.map i (x : E)) (B.map i 1) < eta n := by
    intro n
    have htail : ∀ᶠ i in (U₀ : Filter ℕ), n ≤ i :=
      eventually_of_atTop hcof n (fun _ hi ↦ hi)
    have hfinite : ∀ᶠ i in (U₀ : Filter ℕ), ∀ x : F,
        hsDistSq (B.model i) (B.map i (x : E)) (B.map i 1) < eta n := by
      have hfinite' : ∀ᶠ i in (U₀ : Filter ℕ),
          ∀ x ∈ (Finset.univ : Finset F),
            hsDistSq (B.model i) (B.map i (x : E))
              (B.map i 1) < eta n := by
        rw [eventually_all_finset]
        intro x _
        exact hcloseU x (eta n) (heta n)
      simpa using hfinite'
    exact htail.and hfinite
  let stage : ℕ → ℕ := fun n ↦ Classical.choose (hall n).exists
  have hstage (n : ℕ) :
      n ≤ stage n ∧ ∀ x : F,
        hsDistSq (B.model (stage n))
          (B.map (stage n) (x : E)) (B.map (stage n) 1) < eta n :=
    Classical.choose_spec (hall n).exists
  let B' := B.reindex stage (fun n ↦ (hstage n).1)
  have hsum' : KazhdanCornerMatrices.OpNormVanishing B' (fun n ↦
      ∑ x : F, (B'.map n (x : E) :
        Matrix (B'.model n) (B'.model n) ℂ)) := by
    have hr := FiniteNormalAverageCorner.OpNormVanishing.reindex
      hsum stage (fun n ↦ (hstage n).1)
    change KazhdanCornerMatrices.OpNormVanishing B' _ at hr
    exact hr.congr (fun _ ↦ rfl)
  have hclose' : ∀ x : F,
      FiniteNormalAverageCorner.HSDistVanishing B' (x : E) 1 := by
    intro x epsilon hepsilon
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / epsilon)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hNen : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hsmall : eta n ≤ epsilon := by
      dsimp [eta]
      have hlt : (1 : ℝ) / epsilon < (n : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hepsilon] at hlt
      linarith
    exact le_trans (le_of_lt ((hstage n).2 x)) hsmall
  exact FiniteNormalAverageCorner.false_of_finite_sum_vanishing_of_hsTrivial
    B' F hsum' hclose'

/-! ## Assembly -/

/-- **Assembly of the printed chain.**  No corona representation of a countable
group carrying a Kazhdan conjugation datum detects the central sign
`ε = [t c t⁻¹, ι(a)]²`, proved along the manuscript's route:

`cs_01` (the negative corner) → `cs_02` (transport on the corner) →
`cs_03` (the contradiction).

The two-element subgroup of the printed proof is
`centralInvolutionSubgroup ε`, which is `{1, ε}`; its finiteness and normality
are exactly the printed `ε² = 1` and `ε ∈ Z(H)`, and its distinguished element
is the mark carried by the coordinate lifts. -/
theorem cs_04_no_corona_survival {Γ E : Type} [Group Γ] [Group E] [Countable E]
    (C : KazhdanCompressionCore Γ E) (a : Γ) (z : E)
    (hz : z = ⁅C.transported, C.iota a⁆ ^ 2)
    (hz_sq : z ^ 2 = 1) (hz_central : ∀ g : E, Commute z g)
    (X : ℕ → FiniteModel) (rho : E →* NormMatrixCoronaUnitary X) :
    rho z = 1 := by
  classical
  by_contra hne
  -- Coordinate unitary lifts of the surviving corona representation.
  obtain ⟨A⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one X rho hne
  let F : Subgroup E := centralInvolutionSubgroup z hz_sq
  letI : Finite F := centralInvolutionSubgroup_finite z hz_sq
  letI : Fintype F := Fintype.ofFinite F
  letI : F.Normal := centralInvolutionSubgroup_normal z hz_sq hz_central
  let f : F := ⟨z, involution_mem_centralInvolutionSubgroup z hz_sq⟩
  -- Step 1: the negative corner of the two-element subgroup `{1, z}`.
  obtain ⟨B, hsum⟩ := cs_01_negative_corner F f A
  let U₀ : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U₀ : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  -- Step 2: transport kills the sign on that corner.
  have hzker : z ∈
      ((KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof).ker :=
    MonoidHom.mem_ker.mpr (cs_02_sign_killed C B hcof a z hz)
  have hkillF : ∀ x : F,
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof (x : E) = 1 := by
    intro x
    exact MonoidHom.mem_ker.mp
      ((centralInvolutionSubgroup_le_iff_mem z hz_sq _).mpr hzker x.property)
  -- Step 3: the corner average and the sign cannot both vanish.
  exact cs_03_contradiction F B hcof hsum hkillF
end CentralSignTransport
end GroupApproximation
