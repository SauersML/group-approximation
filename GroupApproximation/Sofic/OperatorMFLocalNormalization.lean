import GroupApproximation.Sofic.OperatorMFPairAmplification
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Local separation normalization for operator-MF groups

This is the finite-pair tensor-amplification argument, decomposed into small
declarations.  For each ordered distinct pair in a finite test set, choose a
corona coordinate on which that pair is separated while all required products
are accurate.  A bounded tensor power makes the pair more than distance one
apart.  The finite block sum of these pair-specific models keeps the same
multiplicative error and separates every distinct pair by at least one.
-/

namespace GroupApproximation
namespace OperatorMFLocalNormalization

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Distinct images in a norm corona have a positive pairwise gap on
frequently many coordinates of arbitrary unitary lifts. -/
theorem frequently_pair_separated
    {X : ℕ → FiniteModel}
    (rho : G →* NormMatrixCoronaUnitary X)
    (hrho : Function.Injective rho)
    (lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g)
    {g h : G} (hgh : g ≠ h) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n in Filter.cofinite,
      δ ≤ ‖(lift g n : Matrix (X n) (X n) ℂ) - lift h n‖ := by
  have hrhone : rho g ≠ rho h := fun heq ↦ hgh (hrho heq)
  have hnot : (lift g)⁻¹ * lift h ∉ nullCofiniteOpSubgroup X := by
    intro hmem
    apply hrhone
    rw [← hlift g, ← hlift h]
    exact QuotientGroup.eq.mpr hmem
  have hex : ∃ δ : ℝ, 0 < δ ∧
      ¬ ∀ᶠ n in Filter.cofinite,
        opLength (X n) (((lift g)⁻¹ * lift h) n) < δ := by
    by_contra hcon
    apply hnot
    intro δ hδ
    by_contra hbad
    exact hcon ⟨δ, hδ, hbad⟩
  obtain ⟨δ, hδ, hfrequent⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  show ¬ ∀ᶠ n in Filter.cofinite,
    ¬ δ ≤ ‖(lift g n : Matrix (X n) (X n) ℂ) - lift h n‖
  simpa only [Pi.mul_apply, Pi.inv_apply, not_le, opLength_inv_mul,
    norm_sub_rev] using hfrequent

/-- Proof-carrying coordinate and tensor exponent for one designated pair. -/
structure PairStage
    {X : ℕ → FiniteModel}
    (lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (F : Finset G) (ε : ℝ) (g h : G) where
  N : ℕ
  n : ℕ
  p : ℕ
  N_pos : 0 < (N : ℝ)
  model_nonempty : Nonempty (X n)
  p_le_N : p ≤ N
  base_multiplicative : ∀ r ∈ F, ∀ s ∈ F,
    ‖(lift (r * s) n : Matrix (X n) (X n) ℂ) -
      (lift r n : Matrix (X n) (X n) ℂ) * lift s n‖ ≤ ε / N
  tensor_separated :
    1 < ‖opTensorPow (lift g n : Matrix (X n) (X n) ℂ) p -
      opTensorPow (lift h n : Matrix (X n) (X n) ℂ) p‖

/-- Select the coordinate and bounded tensor exponent for one pair. -/
theorem exists_pairStage
    {X : ℕ → FiniteModel} (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X)
    (hrho : Function.Injective rho)
    (lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g)
    (F : Finset G) {ε : ℝ} (hε : 0 < ε)
    {g h : G} (hgh : g ≠ h) :
    Nonempty (PairStage lift F ε g h) := by
  classical
  obtain ⟨δ, hδ, hsep⟩ :=
    frequently_pair_separated rho hrho lift hlift hgh
  obtain ⟨N, hNraw⟩ := exists_nat_gt (8 / δ ^ 2)
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hN : 8 < (N : ℝ) * δ ^ 2 := by
    rwa [div_lt_iff₀ hδsq] at hNraw
  have hNpos : 0 < (N : ℝ) := by
    by_contra hnonpos
    have hle : (N : ℝ) * δ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnonpos) (sq_nonneg δ)
    linarith
  have hmul : ∀ᶠ n in Filter.cofinite,
      ∀ r ∈ F, ∀ s ∈ F,
        ‖(lift (r * s) n : Matrix (X n) (X n) ℂ) -
          (lift r n : Matrix (X n) (X n) ℂ) * lift s n‖ ≤ ε / N := by
    rw [eventually_all_finset]
    intro r _hr
    rw [eventually_all_finset]
    intro s _hs
    exact normMatrixCorona_lift_eventually_multiplicative X rho lift hlift
      r s (ε / N) (div_pos hε hNpos)
  obtain ⟨n, hnsep, hnmul⟩ := (hsep.and_eventually hmul).exists
  letI : Nonempty (X n) := Fintype.card_pos_iff.mp (hX n)
  obtain ⟨p, _hp1, hpN, hpsep⟩ :=
    OperatorNormAmplification.exists_tensorPower_pair_far
      inferInstance (lift g n).property (lift h n).property hδ hnsep N hN
  exact ⟨{
    N := N
    n := n
    p := p
    N_pos := hNpos
    model_nonempty := inferInstance
    p_le_N := hpN
    base_multiplicative := hnmul
    tensor_separated := hpsep }⟩

namespace PairStage

variable {X : ℕ → FiniteModel}
  {lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ}
  {F : Finset G} {ε : ℝ} {g h : G}

/-- The tensor-amplified unitary block encoded by a pair stage. -/
def block (S : PairStage lift F ε g h) : UnitaryBlock G where
  model := opTensorModel (X S.n) S.p
  map r := ⟨opTensorPow (lift r S.n : Matrix (X S.n) (X S.n) ℂ) S.p,
    opTensorPow_mem_unitaryGroup (lift r S.n).property S.p⟩

theorem block_model_pos (S : PairStage lift F ε g h) :
    0 < Fintype.card S.block.model := by
  rw [Fintype.card_pos_iff]
  letI : Nonempty (X S.n) := S.model_nonempty
  exact ⟨opTensorRepeat (Classical.choice inferInstance) S.p⟩

theorem block_multiplicative (S : PairStage lift F ε g h)
    (hε : 0 < ε) {r s : G} (hr : r ∈ F) (hs : s ∈ F) :
    ‖(S.block.map (r * s) : Matrix S.block.model S.block.model ℂ) -
      S.block.map r * S.block.map s‖ ≤ ε := by
  letI : Nonempty (X S.n) := S.model_nonempty
  change ‖opTensorPow (lift (r * s) S.n : Matrix (X S.n) (X S.n) ℂ) S.p -
    opTensorPow (lift r S.n : Matrix (X S.n) (X S.n) ℂ) S.p *
      opTensorPow (lift s S.n : Matrix (X S.n) (X S.n) ℂ) S.p‖ ≤ ε
  rw [← opTensorPow_mul]
  calc
    ‖opTensorPow (lift (r * s) S.n : Matrix (X S.n) (X S.n) ℂ) S.p -
        opTensorPow ((lift r S.n : Matrix (X S.n) (X S.n) ℂ) *
          (lift s S.n : Matrix (X S.n) (X S.n) ℂ)) S.p‖
        ≤ S.p * ‖(lift (r * s) S.n : Matrix (X S.n) (X S.n) ℂ) -
          (lift r S.n : Matrix (X S.n) (X S.n) ℂ) *
            (lift s S.n : Matrix (X S.n) (X S.n) ℂ)‖ :=
      l2_opNorm_opTensorPow_sub_le inferInstance (lift (r * s) S.n).property
        (mul_mem (lift r S.n).property (lift s S.n).property) S.p
    _ ≤ S.p * (ε / S.N) :=
      mul_le_mul_of_nonneg_left (S.base_multiplicative r hr s hs)
        (Nat.cast_nonneg S.p)
    _ ≤ ε := by
      have hpN : (S.p : ℝ) ≤ S.N := by exact_mod_cast S.p_le_N
      calc
        (S.p : ℝ) * (ε / S.N) = ((S.p : ℝ) / S.N) * ε := by ring
        _ ≤ 1 * ε := mul_le_mul_of_nonneg_right
          ((div_le_one S.N_pos).2 hpN) hε.le
        _ = ε := one_mul ε

theorem block_separated (S : PairStage lift F ε g h) :
    1 < ‖(S.block.map g : Matrix S.block.model S.block.model ℂ) -
      S.block.map h‖ :=
  S.tensor_separated

end PairStage

/-- **Separation normalization.** Every operator-MF group admits local
operator-norm models with separation constant exactly one. -/
theorem isNormApproximable_one (hMF : IsOperatorMF G) :
    IsNormApproximable G 1 := by
  classical
  intro F ε hε
  obtain ⟨X, hX, rho, hrho⟩ := hMF
  choose lift hlift using fun x : G ↦ QuotientGroup.mk_surjective (rho x)
  let pairs : Finset (G × G) := (F ×ˢ F).filter fun q ↦ q.1 ≠ q.2
  let Pair : Type u := {q : G × G // q ∈ pairs}
  have hstage (q : Pair) :
      Nonempty (PairStage lift F ε q.1.1 q.1.2) := by
    have hne : q.1.1 ≠ q.1.2 := by
      have hq := q.2
      simp only [pairs, Finset.mem_filter, Finset.mem_product] at hq
      exact hq.2
    exact exists_pairStage hX rho hrho lift hlift F hε hne
  let stage : ∀ q : Pair, PairStage lift F ε q.1.1 q.1.2 :=
    fun q ↦ Classical.choice (hstage q)
  let trivial : UnitaryBlock G := {
    model := ⟨PUnit, inferInstance, inferInstance⟩
    map := fun _ ↦ 1 }
  let blocks : List (UnitaryBlock G) :=
    trivial :: (Finset.univ : Finset Pair).toList.map fun q ↦ (stage q).block
  refine ⟨{
    carrier := blockListModel blocks
    nonempty := card_blockListModel_pos_of_mem
      (show trivial ∈ blocks by simp [blocks]) (by simp [trivial])
    map := blockListMap blocks
    isUnitary := blockListMap_mem_unitaryGroup blocks
    multiplicative := ?_
    separated := ?_ }⟩
  · intro r hr s hs
    apply norm_blockListMap_mul_sub_le G blocks r s hε.le
    intro B hB
    rw [show blocks = trivial ::
        (Finset.univ : Finset Pair).toList.map
          (fun q ↦ (stage q).block) by rfl] at hB
    rcases List.mem_cons.mp hB with rfl | hB
    · simpa [trivial] using hε.le
    · rw [List.mem_map] at hB
      obtain ⟨q, _hq, rfl⟩ := hB
      exact (stage q).block_multiplicative hε hr hs
  · intro r hr s hs hrs
    have hqmem : (r, s) ∈ pairs := by simp [pairs, hr, hs, hrs]
    let q : Pair := ⟨(r, s), hqmem⟩
    have hmem : (stage q).block ∈ blocks := by
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      exact ⟨q, by simp, rfl⟩
    exact (le_of_lt (stage q).block_separated).trans
      (norm_blockListMap_sub_ge_of_mem hmem r s)

/-- On countable groups, standard operator-MF is equivalent to normalized
local operator-norm approximability. -/
theorem isOperatorMF_iff_isNormApproximable_one [Countable G] :
    IsOperatorMF G ↔ IsNormApproximable G 1 := by
  constructor
  · exact isNormApproximable_one
  · intro h
    exact (show IsWeakMF G from ⟨1, by norm_num, h⟩).isOperatorMF

end

end OperatorMFLocalNormalization
end GroupApproximation
