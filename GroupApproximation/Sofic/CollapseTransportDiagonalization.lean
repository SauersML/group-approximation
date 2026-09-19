import GroupApproximation.Sofic.InvolutionCollapseEndpointPrep

/-!
# Diagonalizing the approximate coboundary primitives of the collapse

**Manuscript reference.** `non_mf_groups_exist.tex`,
`\subsection{Orbit collapse and defect saturation}\label{subsec:collapse}`,
Theorem `thm:collapse`, Steps 5 and 6 of the printed proof sketch, together
with the discussion after `thm:transport-variants` ("the collapse proof of
Theorem `thm:collapse` uses a rank weight, which normalizes a defect at its
own scale").  In the step-for-step audit `notes/COLLAPSE_STEP_AUDIT.md` this
is finding **R1**, route **(b)**.

**The defect this module closes.**  Step 5 of the sketch produces an
approximate primitive for the displacement cocycle, and Step 6 transports it
"as in Theorem `thm:kazhdan-transport`", i.e. at the rank weight through
`thm:transport-variants`(1).  In Lean the Step-5 primitive is
`InvolutionCollapseCenter.exists_approximate_coboundary`, which delivers a
bounded sequence whose coboundary defect is below **one tolerance `δ` fixed
in advance**; whereas the cited transport theorem
(`ScaledKazhdanTransport.scaled_transport_both`, and equally
`UltraproductScaledTransport.scaled_transport_both_of_ambient`) consumes
`IsScaledAsymptoticCommutantOf`, defined through `ScaledMassVanishing`, i.e.
a displacement below `ε · wₙ` **for every** `ε`.  The qualitative hypothesis
is therefore unavailable and the endpoint re-derives Step 6 inline.

Contents:

* `exists_diagonal_level` — the combinatorial core.  A countable family of
  hyperfilter-large stage predicates admits a level assignment `jj` which
  satisfies its own level's predicate at every stage where it is positive,
  and which dominates each fixed level hyperfilter-eventually.
* `exists_vanishing_coboundary_primitive` — one bounded sequence `w`, with
  the stagewise bound `‖wₙ‖ ≤ √R + 2 = C_w` at **every** stage, whose
  coboundary defect against `bVec` has limiting squared seminorm **exactly
  zero** at every mover of the prescribed finite set `T` (in the collapse,
  `T = S ∪ sSs⁻¹`).  This is the literal reading of the manuscript's
  Step 5 → Step 6 interface.
* `exists_cofinal_vanishing_coboundary_primitive` — the same primitive read
  along a cofinal reindexing `φ` (`n ≤ φ n`, the hypothesis of
  `OpAlmostRepresentation.reindex`), where the defect bound now holds at
  **every** stage with the explicit rate `2/(j+1)`.
* `isScaledMassBounded_rankScaled`, `scaledMassVanishing_rankScaled` — the
  rank-weight packaging: with `xⱼ = √wⱼ · unflat(Wⱼ)` and weight
  `wⱼ = k_{φ j}`, the primitive is mass bounded by `C_w² · wⱼ` at every
  stage, and its displacement along a mover whose `bVec` eventually vanishes
  is scaled-mass null.  These are exactly the two hypotheses of
  `ScaledKazhdanTransport.scaled_transport_both` at weight `k`.

**Module note on filters — why the cofinal reindexing is not optional.**
`Ultralimit.seqNormSq` is a standard part along `Filter.hyperfilter ℕ`, while
`ScaledKazhdanTransport.ScaledMassVanishing` is an `∃ N, ∀ n ≥ N` statement,
i.e. eventual along `Filter.atTop`.  Since `hyperfilter ≤ cofinite = atTop`
on `ℕ`, an `atTop` statement implies its hyperfilter counterpart but never
conversely: a hyperfilter-large set can omit an infinite set of stages, and
about those stages the circumcenter of Step 5 says nothing at all.  So no
bounded sequence on the *original* index set need have `atTop`-vanishing
defect, and `exists_vanishing_coboundary_primitive` alone cannot feed the
transport theorem.  Reading the primitive along a cofinal subsequence is the
repair, and it is the manuscript's own maneuver — the proof of `thm:collapse`
opens by passing to a subsequence.
-/

namespace GroupApproximation
namespace CollapseTransportDiagonalization

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open InvolutionCollapseMetric InvolutionMicrostateTools
open InvolutionCollapseProfile InvolutionCollapseCocycle
open InvolutionCollapseCenter InvolutionCollapseEndpointPrep
open Ultralimit KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

/-! ## Flattening bookkeeping

Local copies of facts that live downstream in
`Sofic.InvolutionCollapseEndpoint`; this module must sit *below* the endpoint
in the import order, since the endpoint is what will consume it. -/

/-- The flattening isometry is inverse to unflattening. -/
theorem flatE_unflatE {Y : Type*} [Fintype Y]
    (x : EuclideanSpace ℂ (Y × Y)) : flatE (unflatE x) = x := by
  ext p
  rfl

/-- The Frobenius mass of a real rescaling of an unflattened vector. -/
theorem matMass_smul_unflatE {Y : Type*} [Fintype Y] (r : ℝ)
    (v : EuclideanSpace ℂ (Y × Y)) :
    ScaledKazhdanTransport.matMass ((r : ℂ) • unflatE v) =
      r ^ 2 * ‖v‖ ^ 2 := by
  have hbase : ScaledKazhdanTransport.matMass (unflatE v) = ‖v‖ ^ 2 := by
    rw [← norm_flatE_sq, flatE_unflatE]
  rw [ScaledKazhdanTransport.matMass_smul, Complex.normSq_ofReal, hbase]
  ring

/-- The Frobenius mass of the adjoint displacement of a real rescaling of an
unflattened vector, in terms of the flattened adjoint action `adFlat`. -/
theorem matMass_smul_unflatE_displacement {Y : Type*} [Fintype Y]
    (r : ℝ) (U : Matrix Y Y ℂ)
    (v : EuclideanSpace ℂ (Y × Y)) :
    ScaledKazhdanTransport.matMass
        ((r : ℂ) • unflatE v - U * ((r : ℂ) • unflatE v) * Uᴴ) =
      r ^ 2 * ‖v - adFlat U v‖ ^ 2 := by
  have hpull : U * ((r : ℂ) • unflatE v) * Uᴴ =
      (r : ℂ) • (U * unflatE v * Uᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hflat : v - adFlat U v = flatE (unflatE v - U * unflatE v * Uᴴ) := by
    rw [flatE_sub, flatE_unflatE, adFlat]
  rw [hpull, ← smul_sub, ScaledKazhdanTransport.matMass_smul,
    Complex.normSq_ofReal, hflat, norm_flatE_sq]
  ring

/-! ## Hyperfilter bookkeeping -/

/-- A hyperfilter-eventual property holds at arbitrarily late stages: a
hyperfilter-large set of indices is cofinal in `ℕ`. -/
theorem exists_ge_of_hyperfilter_eventually {P : ℕ → Prop}
    (h : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), P n) (N : ℕ) :
    ∃ n, N ≤ n ∧ P n :=
  ((eventually_le_id N).and h).exists

/-- A squared-norm bound holding hyperfilter-eventually bounds the limiting
squared seminorm. -/
theorem seqNormSq_le_of_eventually {H : ℕ → Type*}
    [∀ n, NormedAddCommGroup (H n)] {v : ∀ n, H n}
    (hv : IsBoundedSeq v) {c : ℝ}
    (h : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ‖v n‖ ^ 2 ≤ c) :
    seqNormSq v ≤ c := by
  have hle : (Hyperreal.ofSeq fun n ↦ ‖v n‖ ^ 2) ≤ ((c : ℝ) : Hyperreal) := by
    change _ ≤ Hyperreal.ofSeq (fun _ : ℕ ↦ c)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact h
  rw [seqNormSq_def]
  exact ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom
    (ofSeq_norm_sq_finite hv) hle

/-- A nonnegative real below every term of the null sequence `2/(j+1)` is
zero.  This is where the tolerance diagonalization actually converges. -/
theorem eq_zero_of_le_two_div {c : ℝ} (h0 : 0 ≤ c)
    (h : ∀ j : ℕ, c ≤ 2 * (1 / ((j : ℝ) + 1))) : c = 0 := by
  have htend : Filter.Tendsto (fun j : ℕ ↦ 2 * (1 / ((j : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hle : c ≤ 0 := ge_of_tendsto' htend h
  linarith

/-- The explicit rate `2/(j+1)` falls below any prescribed `ε` from some
level on. -/
theorem exists_level_two_div_le {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j ≥ J, 2 * (1 / ((j : ℝ) + 1)) ≤ ε := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 / ε)
  refine ⟨J, fun j hj ↦ ?_⟩
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hJj : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h2 : 2 / ε < (j : ℝ) + 1 := by linarith
  have h3 : (2 : ℝ) < ((j : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h2
  have hc : ((j : ℝ) + 1) * ε = ε * ((j : ℝ) + 1) := mul_comm _ _
  rw [mul_one_div, div_le_iff₀ hj1]
  linarith

/-- **The diagonal level assignment.**  Given a countable family of
hyperfilter-large stage predicates, there is a level function `jj` which, at
every stage where it is positive, satisfies its own level's predicate, and
which dominates each fixed level hyperfilter-eventually.  This is the
combinatorial core of the tolerance diagonalization: it is the reason a
*single* sequence can inherit *every* tolerance at once. -/
theorem exists_diagonal_level (A : ℕ → ℕ → Prop)
    (hA : ∀ j, ∀ᶠ n in ↑(Filter.hyperfilter ℕ), A j n) :
    ∃ jj : ℕ → ℕ, (∀ n, jj n ≠ 0 → A (jj n) n) ∧
      ∀ j, ∀ᶠ n in ↑(Filter.hyperfilter ℕ), j ≤ jj n := by
  classical
  refine ⟨fun n ↦ Nat.findGreatest (fun j ↦ j = 0 ∨ A j n) n, ?_, ?_⟩
  · intro n hn
    have hspec :
        (Nat.findGreatest (fun j ↦ j = 0 ∨ A j n) n = 0) ∨
          A (Nat.findGreatest (fun j ↦ j = 0 ∨ A j n) n) n :=
      Nat.findGreatest_spec (P := fun j ↦ j = 0 ∨ A j n)
        (Nat.zero_le n) (Or.inl rfl)
    rcases hspec with hzero | hgood
    · exact absurd hzero hn
    · exact hgood
  · intro j
    filter_upwards [hA j, eventually_le_id j] with n hn hjn
    exact Nat.le_findGreatest hjn (Or.inr hn)

/-! ## Boundedness of the coboundary defect

Local copies of `InvolutionCollapseEndpoint.ydiff_bounded` and
`InvolutionCollapseEndpoint.xdiff_bounded`, for the same import-order
reason. -/

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)
variable (S : Finset Γ)

/-- The coboundary difference of a bounded sequence is bounded. -/
theorem boundedSeq_coboundary
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)) := by
  obtain ⟨Cb, hCb⟩ := id hwbdd
  refine ⟨Cb + Cb, fun n ↦ ?_⟩
  have hiso : ‖adFlat (B.map n (iota a) :
      Matrix (B.model n) (B.model n) ℂ) (w n)‖ = ‖w n‖ :=
    norm_adFlat (B.map n (iota a)).2 _
  calc
    ‖w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)‖ ≤
        ‖w n‖ + ‖adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
    _ ≤ Cb + Cb := by
      rw [hiso]
      exact add_le_add (hCb n) (hCb n)

/-- The coboundary defect of a bounded sequence against the displacement
cocycle is bounded. -/
theorem boundedSeq_defect
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    {w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n)}
    (hwbdd : IsBoundedSeq w) (a : Γ) :
    IsBoundedSeq (fun n ↦
      bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))) := by
  obtain ⟨Ca, hCa⟩ :=
    id (isBoundedSeq_bVec B V S hgen hsymm hVinv hVcomm a)
  obtain ⟨Cy, hCy⟩ := id (boundedSeq_coboundary B iota hwbdd a)
  refine ⟨Ca + Cy, fun n ↦ ?_⟩
  calc
    ‖bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))‖ ≤
        ‖bVec B V S hgen hsymm n a‖ +
          ‖w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n)‖ := norm_sub_le _ _
    _ ≤ Ca + Cy := add_le_add (hCa n) (hCy n)

/-! ## The diagonalized primitive -/

/-- **Step 5 → Step 6, route (b): a single primitive with vanishing
coboundary defect.**  Applying
`InvolutionCollapseCenter.exists_approximate_coboundary` at the tolerances
`δⱼ = 1/(j+1)` and diagonalizing over the resulting hyperfilter-large stage
sets produces one sequence `w`, bounded by `C_w = √R + 2` at *every* stage,
whose coboundary defect against the displacement cocycle has limiting squared
seminorm **zero** at every mover of the prescribed finite set `T`.

This is the manuscript's literal Step 5 → Step 6 interface: the primitive of
Step 5 is exact in the limit, so Step 6 may cite `thm:kazhdan-transport`.  It
is a hyperfilter statement; see `exists_cofinal_vanishing_coboundary_primitive`
for the form that `ScaledMassVanishing` can consume. -/
theorem exists_vanishing_coboundary_primitive
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ : Γ, seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R)
    (T : Finset Γ) :
    ∃ w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n),
      (∀ n, ‖w n‖ ≤ Real.sqrt R + 2) ∧
      ∀ a ∈ T, seqNormSq (fun n ↦
        bVec B V S hgen hsymm n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) = 0 := by
  classical
  -- the family of `δⱼ`-approximate primitives, `δⱼ = 1/(j+1)`
  have hfam : ∀ j : ℕ,
      ∃ u : ∀ n, EuclideanSpace ℂ (B.model n × B.model n),
        IsBoundedSeq u ∧ seqNorm u ≤ Real.sqrt R + 1 ∧
        ∀ a ∈ T, seqNormSq (fun n ↦
          bVec B V S hgen hsymm n a -
            (u n - adFlat (B.map n (iota a) :
              Matrix (B.model n) (B.model n) ℂ) (u n))) ≤
          1 / ((j : ℝ) + 1) := by
    intro j
    exact exists_approximate_coboundary_of_data B iota k V S hgen hsymm hVinv
      hVcomm hVconv hmark hR0 hR T (by positivity)
  choose u hub hun huc using hfam
  -- the stage predicate at level `j`
  set P : ℕ → ℕ → Prop := fun j n ↦
    (∀ a ∈ T, ‖bVec B V S hgen hsymm n a -
        (u j n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (u j n))‖ ^ 2 ≤
      2 * (1 / ((j : ℝ) + 1))) ∧
    ‖u j n‖ ≤ Real.sqrt R + 2 with hPdef
  have hPlarge : ∀ j, ∀ᶠ n in ↑(Filter.hyperfilter ℕ), P j n := by
    intro j
    have hdpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hfirst : ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ T,
        ‖bVec B V S hgen hsymm n a -
            (u j n - adFlat (B.map n (iota a) :
              Matrix (B.model n) (B.model n) ℂ) (u j n))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1)) := by
      rw [Filter.eventually_all_finset]
      intro a haT
      have hbnd := boundedSeq_defect B iota V S hgen hsymm hVinv hVcomm
        (hub j) a
      filter_upwards [eventually_norm_le_of_seqNormSq_le hbnd
        (huc j a haT) hdpos] with n hn
      have hnn := norm_nonneg (bVec B V S hgen hsymm n a -
        (u j n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (u j n)))
      have hsq : Real.sqrt (2 * (1 / ((j : ℝ) + 1))) ^ 2 =
          2 * (1 / ((j : ℝ) + 1)) := Real.sq_sqrt (by positivity)
      nlinarith [hn, hnn, hsq, Real.sqrt_nonneg (2 * (1 / ((j : ℝ) + 1)))]
    have hsecond : ∀ᶠ n in ↑(Filter.hyperfilter ℕ),
        ‖u j n‖ ≤ Real.sqrt R + 2 := by
      have hlt : seqNorm (u j) < Real.sqrt R + 2 := by
        have := hun j
        linarith
      filter_upwards [eventually_norm_lt_of_seqNorm_lt (hub j) hlt] with n hn
      exact hn.le
    filter_upwards [hfirst, hsecond] with n hn1 hn2
    simp only [hPdef]
    exact ⟨hn1, hn2⟩
  obtain ⟨jj, hjjmem, hjjbig⟩ := exists_diagonal_level P hPlarge
  -- the diagonal sequence: at each stage, use the deepest tolerance that
  -- stage is good for
  obtain ⟨w, hwn, hwval⟩ :
      ∃ w : ∀ n, EuclideanSpace ℂ (B.model n × B.model n),
        (∀ n, ‖w n‖ ≤ Real.sqrt R + 2) ∧
        (∀ n, jj n ≠ 0 → w n = u (jj n) n) := by
    refine ⟨fun n ↦ if jj n = 0 then 0 else u (jj n) n, fun n ↦ ?_,
      fun n hn ↦ ?_⟩
    · show ‖(if jj n = 0 then
          (0 : EuclideanSpace ℂ (B.model n × B.model n))
        else u (jj n) n)‖ ≤ Real.sqrt R + 2
      split_ifs with h0
      · rw [norm_zero]
        positivity
      · have hmem := hjjmem n h0
        simp only [hPdef] at hmem
        exact hmem.2
    · show (if jj n = 0 then
          (0 : EuclideanSpace ℂ (B.model n × B.model n))
        else u (jj n) n) = u (jj n) n
      rw [if_neg hn]
  refine ⟨w, hwn, fun a haT ↦ ?_⟩
  have hwb : IsBoundedSeq w := ⟨Real.sqrt R + 2, hwn⟩
  have hdb := boundedSeq_defect B iota V S hgen hsymm hVinv hVcomm hwb a
  refine eq_zero_of_le_two_div ?_ ?_
  · rw [seqNormSq_eq_sq hdb]
    positivity
  · intro j
    refine seqNormSq_le_of_eventually hdb ?_
    filter_upwards [hjjbig (j + 1)] with n hn
    have h0 : jj n ≠ 0 := by omega
    have hjle : j ≤ jj n := by omega
    have hmem := hjjmem n h0
    simp only [hPdef] at hmem
    rw [hwval n h0]
    refine (hmem.1 a haT).trans ?_
    have hcast : ((j : ℝ) + 1) ≤ ((jj n : ℝ) + 1) := by
      have hjr : (j : ℝ) ≤ (jj n : ℝ) := by exact_mod_cast hjle
      linarith
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hmono := one_div_le_one_div_of_le hpos hcast
    linarith

/-- **The cofinal form of the diagonalization.**  Reading the vanishing
primitive along a cofinal reindexing `φ` (`n ≤ φ n`, the hypothesis of
`OpAlmostRepresentation.reindex`) upgrades the hyperfilter statement to a
stagewise statement with the explicit rate `2/(j+1)`, hence to an `atTop`
statement.  This is the form that `ScaledKazhdanTransport.ScaledMassVanishing`
consumes; passing to a subsequence is the manuscript's own maneuver in the
preamble of the proof of `thm:collapse`. -/
theorem exists_cofinal_vanishing_coboundary_primitive
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (hmark : ∃ N, ∀ n ≥ N, 1 ≤ kNorm B V S n)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ : Γ, seqNormSq (fun n ↦ bVec B V S hgen hsymm n γ) ≤ R)
    (T : Finset Γ) :
    ∃ (φ : ℕ → ℕ)
      (W : ∀ j, EuclideanSpace ℂ (B.model (φ j) × B.model (φ j))),
      (∀ j, j ≤ φ j) ∧ (∀ j, ‖W j‖ ≤ Real.sqrt R + 2) ∧
      ∀ a ∈ T, ∀ j : ℕ,
        ‖bVec B V S hgen hsymm (φ j) a -
          (W j - adFlat (B.map (φ j) (iota a) :
            Matrix (B.model (φ j)) (B.model (φ j)) ℂ) (W j))‖ ^ 2 ≤
          2 * (1 / ((j : ℝ) + 1)) := by
  classical
  obtain ⟨w, hwn, hwvan⟩ := exists_vanishing_coboundary_primitive B iota k V S
    hgen hsymm hVinv hVcomm hVconv hmark hR0 hR T
  have hwb : IsBoundedSeq w := ⟨Real.sqrt R + 2, hwn⟩
  -- at every level the good stages are hyperfilter-large, hence cofinal
  have hgood : ∀ j : ℕ, ∀ᶠ n in ↑(Filter.hyperfilter ℕ), ∀ a ∈ T,
      ‖bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))‖ ^ 2 ≤
        2 * (1 / ((j : ℝ) + 1)) := by
    intro j
    rw [Filter.eventually_all_finset]
    intro a haT
    have hdb := boundedSeq_defect B iota V S hgen hsymm hVinv hVcomm hwb a
    have hdpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hle : seqNormSq (fun n ↦
        bVec B V S hgen hsymm n a -
          (w n - adFlat (B.map n (iota a) :
            Matrix (B.model n) (B.model n) ℂ) (w n))) ≤
        1 / ((j : ℝ) + 1) := by
      rw [hwvan a haT]
      positivity
    filter_upwards [eventually_norm_le_of_seqNormSq_le hdb hle hdpos] with n hn
    have hnn := norm_nonneg (bVec B V S hgen hsymm n a -
      (w n - adFlat (B.map n (iota a) :
        Matrix (B.model n) (B.model n) ℂ) (w n)))
    have hsq : Real.sqrt (2 * (1 / ((j : ℝ) + 1))) ^ 2 =
        2 * (1 / ((j : ℝ) + 1)) := Real.sq_sqrt (by positivity)
    nlinarith [hn, hnn, hsq, Real.sqrt_nonneg (2 * (1 / ((j : ℝ) + 1)))]
  have hchoose : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∀ a ∈ T,
      ‖bVec B V S hgen hsymm n a -
        (w n - adFlat (B.map n (iota a) :
          Matrix (B.model n) (B.model n) ℂ) (w n))‖ ^ 2 ≤
        2 * (1 / ((j : ℝ) + 1)) :=
    fun j ↦ exists_ge_of_hyperfilter_eventually (hgood j) j
  choose φ hφ hφgood using hchoose
  exact ⟨φ, fun j ↦ w (φ j), hφ, fun j ↦ hwn (φ j),
    fun a haT j ↦ hφgood j a haT⟩

/-! ## Rank-weight packaging for `thm:transport-variants`(1)

With `xⱼ = √wⱼ · unflat(Wⱼ)` at weight `wⱼ` (in the collapse
`wⱼ = k_{φ j}`, the rank weight), the two hypotheses of
`ScaledKazhdanTransport.scaled_transport_both` are discharged.  The mass
bound holds at *every* stage, so the finitely many stages with `kₙ = 0` are
covered by the convention of `thm:transport-variants`(1) — there
`xⱼ = 0 • unflat(Wⱼ) = 0`, which is
`UltraproductScaledTransport.eq_zero_of_weight_zero`.

These two statements are deliberately phrased over an arbitrary
`OpAlmostRepresentation` and an arbitrary nonnegative weight, with no
reference to `reindex`: at the call site one instantiates
`B' := B.reindex φ hφ`, `ρ := fun j ↦ (kNorm B V S (φ j) : ℝ)` and
`b := fun j ↦ bVec B V S hgen hsymm (φ j) a`, all of which are definitionally
of the required types. -/

variable (B' : OpAlmostRepresentation E)

/-- The rank-rescaled primitive is mass bounded by `C_w²` at its own weight,
at every stage — including the stages where the weight vanishes. -/
theorem isScaledMassBounded_rankScaled (ρ : ℕ → ℝ) (hρ : ∀ j, 0 ≤ ρ j)
    (W : ∀ j, EuclideanSpace ℂ (B'.model j × B'.model j))
    {Cw : ℝ} (hWn : ∀ j, ‖W j‖ ≤ Cw) :
    ScaledKazhdanTransport.IsScaledMassBounded B' ρ
      (fun j ↦ ((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j)) := by
  refine ⟨Cw ^ 2, sq_nonneg Cw, fun j ↦ ?_⟩
  have hWsq : ‖W j‖ ^ 2 ≤ Cw ^ 2 := by
    nlinarith [norm_nonneg (W j), hWn j]
  have hgoal : ScaledKazhdanTransport.matMass
      (((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j)) ≤ Cw ^ 2 * ρ j := by
    rw [matMass_smul_unflatE, Real.sq_sqrt (hρ j)]
    calc
      ρ j * ‖W j‖ ^ 2 ≤ ρ j * Cw ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (hρ j)
      _ = Cw ^ 2 * ρ j := mul_comm _ _
  exact hgoal

/-- **The transport hypothesis at the rank weight.**  If the displacement
vector `b` eventually vanishes at a mover `g` — which is Step 6's "(W2) makes
the displacement vanish on compressed elements", i.e.
`InvolutionCollapseEndpointPrep.eventually_bVec_eq_zero_of_orbit_fixed` — and
the diagonalized primitive has coboundary defect against `b` at the explicit
rate `2/(j+1)`, then the rescaled primitive has scaled-mass-null displacement
along `g`.  Together with `isScaledMassBounded_rankScaled` this is exactly the
input of `ScaledKazhdanTransport.scaled_transport_both`. -/
theorem scaledMassVanishing_rankScaled (ρ : ℕ → ℝ) (hρ : ∀ j, 0 ≤ ρ j)
    (g : E) (W b : ∀ j, EuclideanSpace ℂ (B'.model j × B'.model j))
    (hb : ∃ N, ∀ j ≥ N, b j = 0)
    (hdef : ∀ j : ℕ,
      ‖b j - (W j - adFlat (B'.map j g :
        Matrix (B'.model j) (B'.model j) ℂ) (W j))‖ ^ 2 ≤
        2 * (1 / ((j : ℝ) + 1))) :
    ScaledKazhdanTransport.ScaledMassVanishing B' ρ
      (fun j ↦
        ((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j) -
          (B'.map j g : Matrix (B'.model j) (B'.model j) ℂ) *
            (((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j)) *
            (B'.map j g : Matrix (B'.model j) (B'.model j) ℂ)ᴴ) := by
  obtain ⟨N, hN⟩ := hb
  intro ε hε
  obtain ⟨J, hJ⟩ := exists_level_two_div_le hε
  refine ⟨max N J, fun j hj ↦ ?_⟩
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  have hjJ : J ≤ j := le_trans (le_max_right _ _) hj
  -- the displacement of the primitive *is* the defect, since `b j = 0`
  have hnormeq :
      ‖W j - adFlat (B'.map j g :
          Matrix (B'.model j) (B'.model j) ℂ) (W j)‖ =
        ‖b j - (W j - adFlat (B'.map j g :
          Matrix (B'.model j) (B'.model j) ℂ) (W j))‖ := by
    rw [hN j hjN, zero_sub, norm_neg]
  have hsmall :
      ‖W j - adFlat (B'.map j g :
        Matrix (B'.model j) (B'.model j) ℂ) (W j)‖ ^ 2 ≤ ε := by
    rw [hnormeq]
    exact (hdef j).trans (hJ j hjJ)
  have hgoal : ScaledKazhdanTransport.matMass
      (((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j) -
        (B'.map j g : Matrix (B'.model j) (B'.model j) ℂ) *
          (((Real.sqrt (ρ j) : ℝ) : ℂ) • unflatE (W j)) *
          (B'.map j g : Matrix (B'.model j) (B'.model j) ℂ)ᴴ) ≤ ε * ρ j := by
    rw [matMass_smul_unflatE_displacement, Real.sq_sqrt (hρ j)]
    calc
      ρ j * ‖W j - adFlat (B'.map j g :
          Matrix (B'.model j) (B'.model j) ℂ) (W j)‖ ^ 2 ≤ ρ j * ε :=
        mul_le_mul_of_nonneg_left hsmall (hρ j)
      _ = ε * ρ j := mul_comm _ _
  exact hgoal

end CollapseTransportDiagonalization
end GroupApproximation
