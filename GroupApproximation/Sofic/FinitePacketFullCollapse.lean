import GroupApproximation.Sofic.FinitePacketCoronaCollapse
import GroupApproximation.Sofic.FinitePacketWordCovariance
import GroupApproximation.Sofic.CollapseScaledStepSix

/-!
# Full finite-packet collapse

This module assembles the generic finite-packet argument.  Exact packet
coordinates, exact covariance, the normalized displacement cocycle, its
bounded Delorme primitive, rank-scaled transport, and the terminal integral
rank collapse are all constructed from the group-theoretic hypotheses.
-/

namespace GroupApproximation
namespace FinitePacketFullCollapse

open Matrix
open FinitePacketCoronaCollapse FinitePacketWordCovariance
open FinitePacketDisplacementCocycle FinitePacketDelormeDiagonalization
open FinitePacketRankWeight FinitePacketCollapseCore
open CollapseTransportDiagonalization CollapseScaledStepSix
open ScaledKazhdanTransport KazhdanCornerMatrices
open InvolutionCollapseCocycle InvolutionRankMass
open KazhdanFiniteModel
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {F : Type u} [Group F] [Fintype F]
variable {Gamma E : Type} [Group Gamma] [Group E]

/-- At the packet rank weight, rescaling the normalized displacement recovers
the original generator displacement, including the zero-weight stages. -/
theorem rankScaled_normalizedDisplacement_eq
    (B : OpAlmostRepresentation E)
    (V : ∀ n, Gamma → Matrix (B.model n) (B.model n) ℂ)
    (S : Finset Gamma) {a : Gamma} (ha : a ∈ S) (n : ℕ) :
    ((Real.sqrt (packetRankWeight B V S n) : ℝ) : ℂ) •
        unflatE (normalizedDisplacement (packetRankWeight B V S) V a n) =
      V n a - V n 1 := by
  classical
  letI : Nonempty (B.model n) :=
    Fintype.card_pos_iff.mp (B.modelNonempty n)
  by_cases hpos : 0 < packetRankWeight B V S n
  · rw [normalizedDisplacement, if_pos hpos, unflatE_real_smul,
      unflatE_flatE]
    have hsqrt : 0 < Real.sqrt (packetRankWeight B V S n) :=
      Real.sqrt_pos.mpr hpos
    rw [smul_comm, ← smul_assoc]
    norm_num [hsqrt.ne']
  · have hwzero : packetRankWeight B V S n = 0 :=
      le_antisymm (le_of_not_gt hpos) (packetRankWeight_nonneg B V S n)
    have hweight : generatorRankWeight (V n) S = 0 := by
      unfold packetRankWeight at hwzero
      exact_mod_cast hwzero
    have hrank : (V n a - V n 1).rank = 0 := by
      have hle := displacementRank_le_generatorRankWeight (V n) S ha
      unfold displacementRank at hle
      omega
    have hmass : matMass (V n a - V n 1) = 0 := by
      apply le_antisymm
      · calc
          matMass (V n a - V n 1) ≤
              ((V n a - V n 1).rank : ℝ) * ‖V n a - V n 1‖ ^ 2 :=
            matMass_le_rank_mul_sq_opNorm _
          _ = 0 := by rw [hrank]; norm_num
      · exact matMass_nonneg _
    have hzero : V n a - V n 1 = 0 :=
      UltraproductScaledTransport.eq_zero_of_matMass_eq_zero hmass
    have hunflatZero : unflatE
        (0 : EuclideanSpace ℂ (B.model n × B.model n)) = 0 := by
      ext i j
      rfl
    rw [normalizedDisplacement, if_neg hpos, hunflatZero, smul_zero, hzero]

/-- **Generic finite-packet corona collapse, with all analytic layers
assembled.**  The statement assumes only the group-theoretic packet,
covariance, property `(T)`, compression, involution, and braid data.  It
constructs exact coordinate packets and a cofinal subsequence on which every
selected packet value is eventually equal to the base value. -/
theorem exists_cofinal_exact_packet_collapse
    (B : OpAlmostRepresentation E)
    (packet : F →* E)
    (iota : Gamma →* E)
    (orbit : Gamma → F)
    (S : Finset Gamma)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Gamma))
    (hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (beta : ↥S → F ≃* F)
    (hcov : ∀ (a : ↥S) f,
      iota (a : Gamma) * packet f * (iota (a : Gamma))⁻¹ = packet (beta a f))
    (horbit : ∀ a : ↥S, ∀ g : Gamma,
      beta a (orbit g) = orbit ((a : Gamma) * g))
    (t : E) (da : Gamma → Gamma)
    (hcompress : ∀ g, t * iota g * t⁻¹ = iota (da g))
    (hfixed : ∀ a ∈ S, orbit (da a) = orbit 1)
    (hinv : ∀ g, orbit g * orbit g = 1)
    (hbraid : ∀ a ∈ S,
      orbit a * orbit 1 * orbit a = orbit 1 * orbit a * orbit 1) :
    ∃ V : ∀ n, F →* Matrix.unitaryGroup (B.model n) ℂ,
      ∃ Uhat : ↥S → ∀ n, Matrix.unitaryGroup (B.model n) ℂ,
        ∃ phi : ℕ → ℕ,
          (∀ j, j ≤ phi j) ∧
          (∀ f, QuotientGroup.mk (fun n ↦ V n f) =
            (OpAlmostRepresentation.coronaHom B) (packet f)) ∧
          (∀ a : ↥S, (QuotientGroup.mk (Uhat a) :
            NormMatrixCoronaUnitary B.model) =
              ((OpAlmostRepresentation.coronaHom B) (iota (a : Gamma)) :
                NormMatrixCoronaUnitary B.model)) ∧
          (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ = V n (beta a f)) ∧
          ∃ N, ∀ j ≥ N, ∀ a ∈ S,
            V (phi j) (orbit a) = V (phi j) (orbit 1) := by
  classical
  have hmodel : ∀ n, Nonempty (B.model n) :=
    fun n ↦ Fintype.card_pos_iff.mp (B.modelNonempty n)
  obtain ⟨V, Uhat, hVlift, hUlift, hcovExact⟩ :=
    FinitePacketCoronaCovariance.exists_exact_covariant_coordinate_lifts_of_ambient
      hmodel (OpAlmostRepresentation.coronaHom B) packet
      (fun a : ↥S ↦ iota (a : Gamma)) beta hcov
  let W : ∀ n, Gamma → Matrix (B.model n) (B.model n) ℂ :=
    fun n g ↦ V n (orbit g)
  let U0 : Gamma → ∀ n, Matrix.unitaryGroup (B.model n) ℂ :=
    fun g n ↦ if hg : g ∈ S then Uhat ⟨g, hg⟩ n else 1
  have hU0lift : ∀ a ∈ S,
      (QuotientGroup.mk (U0 a) : NormMatrixCoronaUnitary B.model) =
        (OpAlmostRepresentation.coronaHom B) (iota a) := by
    intro a ha
    simpa only [U0, dif_pos ha] using hUlift ⟨a, ha⟩
  have hWcovGen : ∀ n a, a ∈ S → ∀ x,
      W n (a * x) =
        (U0 a n : Matrix (B.model n) (B.model n) ℂ) * W n x *
          (U0 a n : Matrix (B.model n) (B.model n) ℂ)ᴴ := by
    intro n a ha x
    have hc := hcovExact n ⟨a, ha⟩ (orbit x)
    have hcval := congrArg Subtype.val hc
    rw [horbit ⟨a, ha⟩ x] at hcval
    dsimp only [W, U0]
    simp only [dif_pos ha]
    exact hcval.symm
  let Uword : ∀ n, Gamma → Matrix.unitaryGroup (B.model n) ℂ :=
    fun n g ↦ wordMoverFamily S hgen U0 g n
  have hUword : ∀ n g,
      (Uword n g : Matrix (B.model n) (B.model n) ℂ) ∈
        Matrix.unitaryGroup (B.model n) ℂ :=
    fun n g ↦ (Uword n g).prop
  have hWcov : ∀ n a x,
      W n (a * x) =
        (Uword n a : Matrix (B.model n) (B.model n) ℂ) * W n x *
          (Uword n a : Matrix (B.model n) (B.model n) ℂ)ᴴ := by
    intro n a x
    exact covariance_wordMover (W n) (fun g ↦ U0 g n) S hgen
      (hWcovGen n) a x
  let rho0 : ℕ → ℝ := packetRankWeight B W S
  have hrho0 : ∀ n, 0 ≤ rho0 n := packetRankWeight_nonneg B W S
  let Cmass : Gamma → ℝ :=
    fun g ↦ 4 * (WordMetric.wordNorm (S : Set Gamma) g : ℝ)
  have hCmass : ∀ g, 0 ≤ Cmass g := by
    intro g
    dsimp [Cmass]
    positivity
  have hmass : ∀ n g,
      matMass (W n g - W n 1) ≤ Cmass g * rho0 n := by
    intro n g
    have hmodel : Nonempty (B.model n) :=
      Fintype.card_pos_iff.mp (B.modelNonempty n)
    have hVunit : ∀ x,
        W n x ∈ Matrix.unitaryGroup (B.model n) ℂ :=
      fun x ↦ (V n (orbit x)).prop
    have hbound := displacementMass_le_four_mul_wordNorm_mul_weight
      hmodel (W n) (fun x ↦ (Uword n x :
        Matrix (B.model n) (B.model n) ℂ)) S hgen hVunit
      (fun a _ ↦ hUword n a) (fun a _ ↦ hWcov n a) g
    simpa only [Cmass, rho0, packetRankWeight] using hbound
  let O : Gamma → ∀ n, EuclideanSpace ℂ (B.model n × B.model n) :=
    normalizedDisplacement rho0 W
  have hOb : ∀ g, Ultralimit.IsBoundedSeq (O g) :=
    isBoundedSeq_normalizedDisplacement rho0 W Cmass hCmass hmass
  have hOone : ∀ n, O 1 n = 0 := normalizedDisplacement_one rho0 W
  have hOdefect : ∀ a g, Ultralimit.seqNorm (fun n ↦
      O g n - (adFlat (Uword n a :
        Matrix (B.model n) (B.model n) ℂ) (O (a⁻¹ * g) n) + O a n)) = 0 :=
    seqNorm_cocycleDefect_eq_zero rho0 W
      (fun n g ↦ (Uword n g : Matrix (B.model n) (B.model n) ℂ)) hWcov
  obtain ⟨Q, kappa, hpair⟩ := hT
  obtain ⟨R, hR0, hR⟩ := exists_uniform_profile_bound rho0 W
    (fun n g ↦ (Uword n g : Matrix (B.model n) (B.model n) ℂ))
    hUword hWcov Cmass hCmass hmass hpair
  let T : Finset Gamma := S ∪ S.image da
  obtain ⟨phi, Z, hphi, hZbound, hZdef⟩ :=
    exists_cofinal_vanishing_coboundary_primitive
      (fun n g ↦ (Uword n g : Matrix (B.model n) (B.model n) ℂ))
      hUword O hOb hOone hOdefect hR0 hR T
  let B' : OpAlmostRepresentation E := B.reindex phi hphi
  let rho : ℕ → ℝ := fun j ↦ rho0 (phi j)
  have hrho : ∀ j, 0 ≤ rho j := fun j ↦ hrho0 (phi j)
  let X : ∀ j, Matrix (B'.model j) (B'.model j) ℂ :=
    fun j ↦ ((Real.sqrt (rho j) : ℝ) : ℂ) • unflatE (Z j)
  let Uword' : Gamma → ∀ j, Matrix.unitaryGroup (B'.model j) ℂ :=
    fun g j ↦ Uword (phi j) g
  have hXbound : IsScaledMassBounded B' rho X := by
    dsimp only [X]
    exact isScaledMassBounded_rankScaled B' rho hrho Z hZbound
  have hop : ∀ g,
      OpNormVanishing B' (fun j ↦
        (Uword' g j : Matrix (B'.model j) (B'.model j) ℂ) -
          (B'.map j (iota g) : Matrix (B'.model j) (B'.model j) ℂ)) := by
    intro g epsilon hepsilon
    have hbase := wordMoverFamily_opNormVanishing B iota U0 S hgen
      hU0lift g epsilon hepsilon
    obtain ⟨N, hN⟩ := hbase
    refine ⟨N, fun j hj ↦ ?_⟩
    exact hN (phi j) (le_trans hj (hphi j))
  have hcompressed : ∀ a ∈ S, ScaledMassVanishing B' rho (fun j ↦
      X j -
        (B'.map j (t * iota a * t⁻¹) :
          Matrix (B'.model j) (B'.model j) ℂ) * X j *
        (B'.map j (t * iota a * t⁻¹) :
          Matrix (B'.model j) (B'.model j) ℂ)ᴴ) := by
    intro a ha
    have hb : ∃ N, ∀ j ≥ N, O (da a) (phi j) = 0 := by
      refine ⟨0, fun j _ ↦ ?_⟩
      dsimp only [O]
      rw [normalizedDisplacement]
      split_ifs
      · have hWeq : W (phi j) (da a) = W (phi j) 1 := by
          dsimp only [W]
          rw [hfixed a ha]
        have hflatZero : InvolutionMicrostateTools.flatE
            (0 : Matrix (B.model (phi j)) (B.model (phi j)) ℂ) = 0 := by
          ext p
          rfl
        rw [hWeq, sub_self, hflatZero, smul_zero]
      · rfl
    have hmem : da a ∈ T := by
      dsimp [T]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem da ha)
    have hexact : ScaledMassVanishing B' rho (fun j ↦
        X j - (Uword' (da a) j :
          Matrix (B'.model j) (B'.model j) ℂ) * X j *
          (Uword' (da a) j : Matrix (B'.model j) (B'.model j) ℂ)ᴴ) := by
      dsimp only [X, Uword']
      exact scaledMassVanishing_rankScaled_unitary B' rho hrho
        (fun j ↦ Uword (phi j) (da a)) Z
        (fun j ↦ O (da a) (phi j)) hb
        (fun j ↦ hZdef (da a) hmem j)
    have hmix := scaled_conjugation_massVanishing_of_opNormVanishing hrho
      (Uword' (da a))
      (fun j ↦ B'.map j (iota (da a))) X hXbound (hop (da a))
    rw [hcompress a]
    exact (hexact.add hmix).congr (fun j ↦ by abel)
  let core : KazhdanCompressionCore Gamma E :=
    { iota := iota
      t := t
      c := 1
      kazhdan := ⟨Q, kappa, hpair⟩
      compresses := fun g ↦ ⟨da g, hcompress g⟩
      comm_c := fun _ ↦ Commute.one_left _ }
  have hcomm : IsScaledAsymptoticCommutant B' rho core X :=
    scaledAsymptoticCommutant_of_conj_vanishing hrho core S hgen.closure_eq
      hXbound hcompressed
  have hvan : ∀ a ∈ S, ScaledMassVanishing B' rho (fun j ↦
      W (phi j) a - W (phi j) 1) := by
    intro a ha epsilon hepsilon
    have hmix := scaled_conjugation_massVanishing_of_opNormVanishing hrho
      (Uword' a) (fun j ↦ B'.map j (iota a))
      X hXbound (hop a)
    have hprimExact : ScaledMassVanishing B' rho (fun j ↦
        X j - (Uword' a j :
          Matrix (B'.model j) (B'.model j) ℂ) * X j *
          (Uword' a j : Matrix (B'.model j) (B'.model j) ℂ)ᴴ) :=
      ((hcomm a).add hmix.sub_symm).congr (fun j ↦ by abel)
    obtain ⟨Np, hNp⟩ := hprimExact (epsilon / 4) (by linarith)
    obtain ⟨Nd, hNd⟩ := exists_level_two_div_le
      (show 0 < epsilon / 4 by linarith)
    refine ⟨max Np Nd, fun j hj ↦ ?_⟩
    have hjp : Np ≤ j := le_trans (le_max_left _ _) hj
    have hjd : Nd ≤ j := le_trans (le_max_right _ _) hj
    have hp := hNp j hjp
    have hp' : rho j * ‖Z j - adFlat (Uword (phi j) a :
        Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j)‖ ^ 2 ≤
        (epsilon / 4) * rho j := by
      have heq := matMass_smul_unflatE_displacement
        (Real.sqrt (rho j))
        (Uword (phi j) a : Matrix (B.model (phi j)) (B.model (phi j)) ℂ)
        (Z j)
      rw [Real.sq_sqrt (hrho j)] at heq
      calc
        rho j * ‖Z j - adFlat (Uword (phi j) a :
            Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j)‖ ^ 2 =
            matMass (((Real.sqrt (rho j) : ℝ) : ℂ) • unflatE (Z j) -
              (Uword (phi j) a :
                Matrix (B.model (phi j)) (B.model (phi j)) ℂ) *
                (((Real.sqrt (rho j) : ℝ) : ℂ) • unflatE (Z j)) *
                (Uword (phi j) a :
                  Matrix (B.model (phi j)) (B.model (phi j)) ℂ)ᴴ) := heq.symm
        _ ≤ (epsilon / 4) * rho j := hp
    have hd := hZdef a (by
      dsimp [T]
      exact Finset.mem_union_left _ ha) j
    have hd' : ‖O a (phi j) -
        (Z j - adFlat (Uword (phi j) a :
          Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j))‖ ^ 2 ≤
        epsilon / 4 := hd.trans (hNd j hjd)
    have hnorm := norm_add_sq_le_two
      (O a (phi j) - (Z j - adFlat (Uword (phi j) a :
        Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j)))
      (Z j - adFlat (Uword (phi j) a :
        Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j))
    have hnorm' : ‖O a (phi j)‖ ^ 2 ≤
        2 * ‖O a (phi j) - (Z j - adFlat (Uword (phi j) a :
          Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j))‖ ^ 2 +
        2 * ‖Z j - adFlat (Uword (phi j) a :
          Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j)‖ ^ 2 := by
      convert hnorm using 1
      abel_nf
    have hrecover := rankScaled_normalizedDisplacement_eq B
      W S ha (phi j)
    calc
      matMass (W (phi j) a - W (phi j) 1) =
          matMass (((Real.sqrt (rho j) : ℝ) : ℂ) •
            unflatE (O a (phi j))) := by
              rw [hrecover]
      _ = rho j * ‖O a (phi j)‖ ^ 2 := by
            rw [matMass_smul_unflatE, Real.sq_sqrt (hrho j)]
      _ ≤ rho j * (2 * ‖O a (phi j) -
            (Z j - adFlat (Uword (phi j) a :
              Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j))‖ ^ 2 +
          2 * ‖Z j - adFlat (Uword (phi j) a :
            Matrix (B.model (phi j)) (B.model (phi j)) ℂ) (Z j)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm' (hrho j)
      _ ≤ epsilon * rho j := by
        nlinarith [mul_le_mul_of_nonneg_left hd' (hrho j), hp']
  let V' : ∀ j, Gamma → Matrix (B'.model j) (B'.model j) ℂ :=
    fun j g ↦ W (phi j) g
  have hVinv : ∀ j g, IsExactInvolution (V' j g) := by
    intro j g
    dsimp [V', W]
    have hsquare : V (phi j) (orbit g) * V (phi j) (orbit g) = 1 := by
      rw [← map_mul, hinv g, map_one]
    have hselfInv : (V (phi j) (orbit g))⁻¹ = V (phi j) (orbit g) :=
      inv_eq_of_mul_eq_one_right hsquare
    constructor
    · calc
        ((V (phi j) (orbit g) : Matrix (B.model (phi j))
            (B.model (phi j)) ℂ)ᴴ) =
            ((V (phi j) (orbit g))⁻¹ :
              Matrix.unitaryGroup (B.model (phi j)) ℂ) := rfl
        _ = (V (phi j) (orbit g) : Matrix (B.model (phi j))
              (B.model (phi j)) ℂ) := congrArg Subtype.val hselfInv
    · exact congrArg Subtype.val hsquare
  have hVbraid : ∀ j a, a ∈ S →
      V' j a * V' j 1 * V' j a = V' j 1 * V' j a * V' j 1 := by
    intro j a ha
    dsimp [V', W]
    have hbGroup :
        V (phi j) (orbit a) * V (phi j) (orbit 1) * V (phi j) (orbit a) =
          V (phi j) (orbit 1) * V (phi j) (orbit a) * V (phi j) (orbit 1) := by
      simpa only [map_mul] using congrArg (V (phi j)) (hbraid a ha)
    exact congrArg Subtype.val hbGroup
  have hvan' : ∀ a ∈ S, ScaledMassVanishing B'
      (packetRankWeight B' V' S) (fun j ↦ V' j a - V' j 1) := by
    intro a ha
    change ScaledMassVanishing B' rho (fun j ↦ W (phi j) a - W (phi j) 1)
    exact hvan a ha
  obtain ⟨N, hN⟩ := eventually_generator_eq_base_of_scaled_vanishing
    B' V' S hVinv hVbraid hvan'
  exact ⟨V, Uhat, phi, hphi, hVlift, hUlift, hcovExact,
    N, fun j hj a ha ↦ Subtype.ext (hN j hj a ha)⟩

end

end FinitePacketFullCollapse
end GroupApproximation
