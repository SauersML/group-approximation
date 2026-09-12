import GroupApproximation.Sofic.CollapseWordMetricBridge
import GroupApproximation.Sofic.InvolutionCollapseCocycle

/-!
# Approximate coboundary primitives from sequence-level circumcenters

The Guichardet step of the collapse: once the profile of the normalized
displacement family is uniformly bounded, the sequence-level circumcenter
machinery of `Kazhdan.UltralimitGeometry` produces one bounded sequence
`w` that is an approximate primitive for the displacement cocycle along
every prescribed finite set of movers simultaneously:

`bVec a ≈ w − adFlat(U_a) w`  in the limiting squared seminorm.

The mechanism: the affine translate `x ↦ adFlat(U_a) x + bVec a` is a
stagewise isometry that almost permutes the displacement orbit (the
coboundary-defect theorem), so it moves a near-optimal covering sequence
of the orbit very little, by the approximate-circumcenter estimate.
-/

namespace GroupApproximation
namespace InvolutionCollapseCenter

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open Ultralimit KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-! ## Sequence-level bookkeeping -/

/-- Stagewise norm bound for the normalized displacement vectors. -/
theorem norm_bVec_le (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (n : ℕ) (γ : Γ) :
    ‖bVec B V S hgen hsymm n γ‖ ≤
      Real.sqrt (4 * (wordLen S hgen hsymm γ : ℝ)) := by
  have hsq := norm_bVec_sq_le B V S hgen hsymm hVinv hVcomm n γ
  have hnn := norm_nonneg (bVec B V S hgen hsymm n γ)
  nlinarith [Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 4 * (wordLen S hgen hsymm γ : ℝ)),
    Real.sqrt_nonneg (4 * (wordLen S hgen hsymm γ : ℝ))]

/-- The displacement vectors of a fixed mover form a bounded sequence. -/
theorem isBoundedSeq_bVec (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (γ : Γ) :
    IsBoundedSeq (fun n ↦ bVec B V S hgen hsymm n γ) :=
  ⟨Real.sqrt (4 * (wordLen S hgen hsymm γ : ℝ)),
    fun n ↦ norm_bVec_le B V S hgen hsymm hVinv hVcomm n γ⟩

/-- A bounded sequence with stagewise vanishing norms has zero
seminorm. -/
theorem seqNorm_eq_zero_of_vanishing {H : ℕ → Type*}
    [∀ n, NormedAddCommGroup (H n)] {v : ∀ n, H n}
    (hb : IsBoundedSeq v)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ‖v n‖ ≤ ε) :
    seqNorm v = 0 := by
  obtain ⟨C, hC⟩ := id hb
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (v 0)) (hC 0)
  have hnormeq := stdPart_ofSeq_eq_of_vanishing
    (x := fun n ↦ ‖v n‖) (y := fun _ ↦ (0 : ℝ)) (C := C)
    (fun n ↦ by rw [abs_of_nonneg (norm_nonneg _)]; exact hC n)
    (fun _ ↦ by rw [abs_of_nonneg le_rfl]; exact hCnn)
    (fun ε hε ↦ by
      obtain ⟨N, hN⟩ := hvan ε hε
      exact ⟨N, fun n hn ↦ by
        rw [sub_zero, abs_of_nonneg (norm_nonneg _)]
        exact hN n hn⟩)
  rw [seqNorm_def, hnormeq,
    show Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) =
      ((0 : ℝ) : Hyperreal) from rfl, stdPart_coe]

/-- Squared seminorms are invariant under stagewise negation. -/
theorem seqNormSq_neg {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
    (v : ∀ n, H n) :
    seqNormSq (fun n ↦ -v n) = seqNormSq v := by
  rw [seqNormSq_def, seqNormSq_def]
  congr 1
  apply congrArg Hyperreal.ofSeq
  funext n
  rw [norm_neg]

/-! ## The approximate coboundary -/

/-- **Approximate coboundary primitives exist.**  If the limiting squared
seminorm of the displacement family is uniformly bounded, there is one
bounded sequence `w` that is a `δ`-approximate primitive for the
displacement cocycle along every mover in any prescribed finite set.

This is the working form, with the data taken as section variables and
leading binders.  The manuscript-facing statement is
`exists_approximate_coboundary` below, which binds all of it after the
colon; the two are the same theorem. -/
theorem exists_approximate_coboundary_of_data
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ : Γ,
      seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R)
    (T : Finset Γ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n),
      IsBoundedSeq w ∧ seqNorm w ≤ Real.sqrt R + 1 ∧
      ∀ a ∈ T, seqNormSq (fun n ↦
        bVec B V S hgen hsymm n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) ≤ δ := by
  classical
  haveI hι : Nonempty Γ := ⟨1⟩
  set O : Γ → ∀ n, EuclideanSpace ℂ (B.model n × B.model n) :=
    fun γ n ↦ bVec B V S hgen hsymm n γ with hO
  have hOb : ∀ γ, IsBoundedSeq (O γ) :=
    fun γ ↦ isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm γ
  set D : ℝ := Real.sqrt R with hD
  have hDnn : 0 ≤ D := Real.sqrt_nonneg R
  have hOD : ∀ γ, seqNorm (O γ) ≤ D := by
    intro γ
    have hsq : seqNorm (O γ) ^ 2 ≤ R := by
      rw [← seqNormSq_eq_sq (hOb γ)]
      exact hR γ
    have hnn : 0 ≤ seqNorm (O γ) := seqNorm_nonneg (hOb γ)
    rw [hD]
    nlinarith [Real.sq_sqrt hR0, Real.sqrt_nonneg R]
  -- the optimal radius is bounded
  have hρD : centerRadius O ≤ D := by
    have hzero : orbitRadius O (fun n ↦ 0) ≤ D := by
      apply orbitRadius_le hι
      intro γ
      have hneg : seqNorm (fun n ↦ (0 : EuclideanSpace ℂ
          (B.model n × B.model n)) - O γ n) = seqNorm (O γ) := by
        have h : (fun n ↦ (0 : EuclideanSpace ℂ
            (B.model n × B.model n)) - O γ n) = fun n ↦ -(O γ n) := by
          funext n
          rw [zero_sub]
        rw [h]
        exact seqNorm_neg (O γ)
      rw [hneg]
      exact hOD γ
    exact (centerRadius_le hι hOb hOD isBoundedSeq_zero).trans hzero
  have hρnn : 0 ≤ centerRadius O := by
    obtain ⟨γ⟩ := id hι
    refine le_csInf ⟨orbitRadius O (O γ), O γ, hOb γ, rfl⟩ ?_
    rintro r ⟨v, hv, rfl⟩
    exact orbitRadius_nonneg hι hOb hOD hv
  -- tolerance for the near-center
  set δ' : ℝ := min 1 (δ / (4 * (2 * D + 1))) with hδ'
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    refine lt_min one_pos ?_
    have h4D : (0 : ℝ) < 4 * (2 * D + 1) := by nlinarith [hDnn]
    exact div_pos hδ h4D
  obtain ⟨v, hv, hvrad⟩ := exists_near_center hι hOb hOD hδ'pos
  have hδ'le1' : δ' ≤ 1 := min_le_left _ _
  have hvnorm : seqNorm v ≤ Real.sqrt R + 1 := by
    have hO1 : ∀ n, O 1 n = 0 :=
      fun n ↦ bVec_one B V S hgen hsymm n
    have h1 : seqNorm v = seqNorm (fun n ↦ v n - O 1 n) := by
      apply seqNorm_congr_norm
      intro n
      rw [hO1 n, sub_zero]
    calc
      seqNorm v = seqNorm (fun n ↦ v n - O 1 n) := h1
      _ ≤ orbitRadius O v := le_orbitRadius hOb hOD hv 1
      _ ≤ centerRadius O + δ' := hvrad.le
      _ ≤ Real.sqrt R + 1 := by
        rw [hD] at hρD
        linarith
  refine ⟨v, hv, hvnorm, fun a haT ↦ ?_⟩
  -- the affine translate of the near-center
  set w' : ∀ n, EuclideanSpace ℂ (B.model n × B.model n) :=
    fun n ↦ adFlat (B.map n (iota a) :
      Matrix (B.model n) (B.model n) ℂ) (v n) + O a n with hw'
  have hw'b : IsBoundedSeq w' := by
    obtain ⟨Cv, hCv⟩ := id hv
    obtain ⟨Ca, hCa⟩ := id (hOb a)
    refine ⟨Cv + Ca, fun n ↦ ?_⟩
    calc
      ‖w' n‖ ≤ ‖adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (v n)‖ + ‖O a n‖ :=
        norm_add_le _ _
      _ ≤ Cv + Ca := by
        rw [norm_adFlat (B.map n (iota a)).2]
        exact add_le_add (hCv n) (hCa n)
  -- the translate still nearly covers the orbit
  have hw'rad : orbitRadius O w' ≤ centerRadius O + δ' := by
    apply orbitRadius_le hι
    intro γ
    -- the coboundary defect at (a, γ)
    set d : ∀ n, EuclideanSpace ℂ (B.model n × B.model n) :=
      fun n ↦ O γ n -
        (adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (O (a⁻¹ * γ) n) + O a n)
      with hd
    have hdb : IsBoundedSeq d := by
      obtain ⟨Cγ, hCγ⟩ := id (hOb γ)
      obtain ⟨Cμ, hCμ⟩ := id (hOb (a⁻¹ * γ))
      obtain ⟨Ca, hCa⟩ := id (hOb a)
      refine ⟨Cγ + (Cμ + Ca), fun n ↦ ?_⟩
      calc
        ‖d n‖ ≤ ‖O γ n‖ +
            ‖adFlat (B.map n (iota a) :
              Matrix (B.model n) (B.model n) ℂ) (O (a⁻¹ * γ) n) +
              O a n‖ := norm_sub_le _ _
        _ ≤ Cγ + (Cμ + Ca) := by
          refine add_le_add (hCγ n) ?_
          calc
            ‖adFlat (B.map n (iota a) :
                Matrix (B.model n) (B.model n) ℂ) (O (a⁻¹ * γ) n) +
                O a n‖ ≤
                ‖adFlat (B.map n (iota a) :
                  Matrix (B.model n) (B.model n) ℂ)
                  (O (a⁻¹ * γ) n)‖ + ‖O a n‖ := norm_add_le _ _
            _ ≤ Cμ + Ca := by
              rw [norm_adFlat (B.map n (iota a)).2]
              exact add_le_add (hCμ n) (hCa n)
    have hdzero : seqNorm d = 0 := by
      refine seqNorm_eq_zero_of_vanishing hdb ?_
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_coboundary_defect_small B iota k V S
        hgen hsymm hVinv hVcomm hVconv hmark a γ hε
      exact ⟨N, fun n hn ↦ hN n hn⟩
    -- decompose the displacement of the translate
    have hsplit : (fun n ↦ w' n - O γ n) =
        fun n ↦ (adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ)
            (v n - O (a⁻¹ * γ) n)) + (-(d n)) := by
      funext n
      rw [hw', hd, adFlat_sub]
      module
    have hisom : seqNorm (fun n ↦ adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (v n - O (a⁻¹ * γ) n)) =
        seqNorm (fun n ↦ v n - O (a⁻¹ * γ) n) := by
      apply seqNorm_congr_norm
      intro n
      exact norm_adFlat (B.map n (iota a)).2 _
    have htriangle := seqNorm_add_le
      (v := fun n ↦ adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (v n - O (a⁻¹ * γ) n))
      (w := fun n ↦ -(d n))
      ⟨(Classical.choose (id (hv.sub (hOb (a⁻¹ * γ))))),
        fun n ↦ by
          rw [norm_adFlat (B.map n (iota a)).2]
          exact Classical.choose_spec
            (id (hv.sub (hOb (a⁻¹ * γ)))) n⟩ hdb.neg
    calc
      seqNorm (fun n ↦ w' n - O γ n) =
          seqNorm (fun n ↦ (adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ)
              (v n - O (a⁻¹ * γ) n)) + (-(d n))) := by rw [hsplit]
      _ ≤ seqNorm (fun n ↦ adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ)
              (v n - O (a⁻¹ * γ) n)) +
          seqNorm (fun n ↦ -(d n)) := htriangle
      _ = seqNorm (fun n ↦ v n - O (a⁻¹ * γ) n) + 0 := by
        rw [hisom, seqNorm_neg, hdzero]
      _ ≤ orbitRadius O v := by
        rw [add_zero]
        exact le_orbitRadius hOb hOD hv (a⁻¹ * γ)
      _ ≤ centerRadius O + δ' := hvrad.le
  -- the stability estimate
  have hstab := seqNormSq_sub_le_of_near_center hι hOb hOD hv hw'b
    (ρ := centerRadius O + δ') hvrad.le hw'rad
  -- convert to the coboundary statement
  have hconv : (fun n ↦ bVec B V S hgen hsymm n a -
      (v n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (v n))) =
      fun n ↦ -(v n - w' n) := by
    funext n
    simp only [hw']
    have hOa : O a n = bVec B V S hgen hsymm n a := rfl
    rw [hOa]
    module
  rw [hconv, seqNormSq_neg]
  refine hstab.trans ?_
  -- numerical bound
  have hδ'le : δ' ≤ δ / (4 * (2 * D + 1)) := min_le_right _ _
  have hδ'le1 : δ' ≤ 1 := min_le_left _ _
  have hexp : 4 * ((centerRadius O + δ') ^ 2 - centerRadius O ^ 2) =
      4 * δ' * (2 * centerRadius O + δ') := by ring
  rw [hexp]
  have hbound : 2 * centerRadius O + δ' ≤ 2 * D + 1 := by
    linarith [hρD, hδ'le1]
  calc
    4 * δ' * (2 * centerRadius O + δ') ≤ 4 * δ' * (2 * D + 1) := by
      have hnn : (0 : ℝ) ≤ 4 * δ' := by linarith [hδ'pos]
      have h0 : 0 ≤ 2 * centerRadius O + δ' := by
        linarith [hρnn, hδ'pos.le]
      nlinarith [hbound]
    _ ≤ 4 * (δ / (4 * (2 * D + 1))) * (2 * D + 1) := by
      have hpos : (0 : ℝ) < 2 * D + 1 := by linarith
      nlinarith [hδ'le, hpos]
    _ = δ := by
      have hne : (4 * (2 * D + 1)) ≠ 0 :=
        ne_of_gt (by nlinarith [hDnn] : (0 : ℝ) < 4 * (2 * D + 1))
      rw [show (4 : ℝ) * (δ / (4 * (2 * D + 1))) * (2 * D + 1) =
        δ * ((4 * (2 * D + 1)) / (4 * (2 * D + 1))) by ring,
        div_self hne, mul_one]

/-- **Approximate coboundary primitives exist**, with every input bound after
the colon.

This is the statement the manuscript prints where it says that the
Delorme--Guichardet bound on the limiting cocycle produces, at each tolerance,
a bounded primitive `w` with `‖w‖ ≤ C+1` satisfying
`‖b_{n_0}(a) - (w_{n_0} - U_{a,n_0} w_{n_0} U_{a,n_0}^{*})‖_{\mathrm F} ≤ τ`
for the finitely many generators.  It takes no declaration input: the group,
the model, the lift family and the mover set are all quantified here rather
than supplied by the section, so the badge on it certifies a closed statement.

**The displacement vector here is the printed one.**  The `b_n` of the display
this badge sits under is `k_n^{-1/2}(V_n(\gamma) - V_n(1))` with no guard, which
is `CollapseWordMetric.bVec`; the working form
`exists_approximate_coboundary_of_data` runs on
`InvolutionCollapseProfile.bVec`, the same vector capped to zero at the stages
before the Step-3 threshold.  Stating this theorem over the capped vector would
badge a different object from the display above it — the defect recorded at
`CO.09` for Step 4, one file over.  The two agree at all large stages for each
fixed mover (`CollapseWordMetricBridge.eventually_profile_bVec_eq`), and both
the hypothesis and the conclusion are limiting squared seminorms, so
`InvolutionCollapseCocycle.seqNormSq_congr_of_eventually_eq` carries the
statement across without reproving anything analytic.

`exists_approximate_coboundary_of_data` is deliberately left as it stands: it
is the working form the endpoint and the diagonalization consume. -/
theorem exists_approximate_coboundary :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (iota : Γ →* E) (k : E)
      (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ) (S : Finset Γ)
      (_hgen : Subgroup.closure (S : Set Γ) = ⊤)
      (_hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
      (_hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
      (_hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
      (_hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
      (_hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
      {R : ℝ} (_hR0 : 0 ≤ R)
      (_hR : ∀ γ : Γ,
        seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) ≤ R)
      (T : Finset Γ) {δ : ℝ} (_hδ : 0 < δ),
      ∃ w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n),
        IsBoundedSeq w ∧ seqNorm w ≤ Real.sqrt R + 1 ∧
        ∀ a ∈ T, seqNormSq (fun n ↦
          CollapseWordMetric.bVec B V S n a -
            (w n - adFlat (B.map n (iota a) :
              Matrix (B.model n) (B.model n) ℂ) (w n))) ≤ δ := by
  intro Γ E _ _ B iota k V S hgen hsymm hVinv hVcomm hVconv hmark R hR0 hR T δ hδ
  -- the printed vectors are bounded sequences
  have hbdp : ∀ γ : Γ,
      IsBoundedSeq (fun n ↦ CollapseWordMetric.bVec B V S n γ) :=
    fun γ ↦ CollapseWordMetric.exists_norm_bVec_bound B iota k V S hgen hsymm
      hVinv hVcomm hVconv γ
  -- the capped and the printed vector have the same limiting profile
  have hcap : ∀ γ : Γ,
      seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) =
        seqNormSq (fun n ↦ CollapseWordMetric.bVec B V S n γ) :=
    fun γ ↦ seqNormSq_congr_of_eventually_eq
      (isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm γ) (hbdp γ)
      (CollapseWordMetricBridge.eventually_profile_bVec_eq B iota k V S hgen
        hsymm hVinv hVcomm hVconv γ)
  have hRcap : ∀ γ : Γ,
      seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R := by
    intro γ
    rw [hcap γ]
    exact hR γ
  obtain ⟨w, hwbdd, hwnorm, hwcob⟩ :=
    exists_approximate_coboundary_of_data B iota k V S hgen hsymm hVinv
      hVcomm hVconv hmark hR0 hRcap T hδ
  refine ⟨w, hwbdd, hwnorm, fun a ha ↦ ?_⟩
  -- the coboundary difference of a bounded primitive is bounded
  have hy : IsBoundedSeq (fun n ↦
      w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) := by
    obtain ⟨Cb, hCb⟩ := id hwbdd
    refine ⟨Cb + Cb, fun n ↦ ?_⟩
    have h3 : ‖adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)‖ = ‖w n‖ := by
      rw [norm_adFlat (B.map n (iota a)).2]
    calc
      ‖w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n)‖ ≤
          ‖w n‖ + ‖adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
      _ ≤ Cb + Cb := by
        rw [h3]
        exact add_le_add (hCb n) (hCb n)
  -- and the two coboundary differences have the same limit
  have hdiff := seqNormSq_congr_of_eventually_eq
    ((isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm a).sub hy)
    ((hbdp a).sub hy)
    (by
      obtain ⟨N, hN⟩ := CollapseWordMetricBridge.eventually_profile_bVec_eq B
        iota k V S hgen hsymm hVinv hVcomm hVconv a
      exact ⟨N, fun n hn ↦ by rw [hN n hn]⟩)
  rw [← hdiff]
  exact hwcob a ha

end InvolutionCollapseCenter
end GroupApproximation
