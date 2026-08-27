import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# Lemma 7.1: the finite-block amplification repair

An operator-norm almost representation separates an element only in `limsup`:
the stages at which `‖U_{b,n} - 1‖` is large may be sparse, and different
elements may be large along different stages.  Section 7.1 repairs this for any
prescribed finite set at once, by taking at each new stage a block sum of old
stages chosen far enough out, one block per tested element.

The block diagonal turns the coordinate defects into their maximum, so
asymptotic multiplicativity survives, while each tested element keeps its own
block and therefore its own lower bound *at every stage*.  This is the
"simultaneous stagewise separation" the corrected removal of condition (iii)
uses in Theorem 7.2.

Fournier-Facio proposed the finite-mover / max-displacement refinement that
this repairs for the norm corona.  His formulation passes to the argmax
subsequence; subsequential vanishing is not vanishing in a `c₀`-corona
(`Sofic.CoronaSubsequence` has the counterexample), and the block amplification
here replaces that step.

The block-list API of `Sofic.NormMFUniversalCorona` does the combinatorial work;
what this file adds is the comparison with the identity block and the choice of
stages.
-/

namespace GroupApproximation

namespace BlockAmplification

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

omit [Group G] in
/-- A block occurring in the list bounds the distance of the whole block
diagonal from the identity: the identity matrix of the sum is the block sum of
identity matrices. -/
theorem norm_blockListMap_sub_one_ge_of_mem {B : UnitaryBlock G}
    {Bs : List (UnitaryBlock G)} (hB : B ∈ Bs) (g : G) :
    ‖(B.map g : Matrix B.model B.model ℂ) - 1‖
      ≤ ‖blockListMap Bs g - 1‖ := by
  induction Bs with
  | nil => simp at hB
  | cons C Cs ih =>
      rw [List.mem_cons] at hB
      have hone : (1 : Matrix (blockListModel (C :: Cs))
          (blockListModel (C :: Cs)) ℂ)
          = blockDiagMatrix C.model (blockListModel Cs) 1 1 :=
        (blockDiagMatrix_one C.model (blockListModel Cs)).symm
      change ‖(B.map g : Matrix B.model B.model ℂ) - 1‖ ≤
        ‖blockDiagMatrix C.model (blockListModel Cs) (C.map g)
            (blockListMap Cs g) - 1‖
      rw [hone, blockDiagMatrix_sub, l2_opNorm_blockDiag]
      rcases hB with rfl | hB
      · exact le_max_left _ _
      · exact (ih hB).trans (le_max_right _ _)

/-- **Lemma 7.1.**  Elements separated in `limsup` by an almost representation
are separated *at every stage* by an amplified one, simultaneously across any
prescribed finite set. -/
theorem exists_stagewise_separated (A : OpAlmostRepresentation G)
    (bs : Finset G) (c : G → ℝ) (hc : ∀ b ∈ bs, 0 < c b)
    (hfreq : ∀ b ∈ bs, ∀ N : ℕ, ∃ n, N ≤ n ∧
      c b ≤ ‖(A.map n b : Matrix (A.model n) (A.model n) ℂ) - 1‖) :
    ∃ (A' : OpAlmostRepresentation G) (η : ℝ), 0 < η ∧
      ∀ b ∈ bs, ∀ k : ℕ,
        η ≤ ‖(A'.map k b : Matrix (A'.model k) (A'.model k) ℂ) - 1‖ := by
  classical
  rcases Finset.eq_empty_or_nonempty bs with rfl | hbs
  · exact ⟨A, 1, one_pos, by simp⟩
  -- one stage per tested element, chosen beyond the current stage
  have hpick : ∀ (b : G) (N : ℕ), ∃ n, N ≤ n ∧ (b ∈ bs →
      c b ≤ ‖(A.map n b : Matrix (A.model n) (A.model n) ℂ) - 1‖) := by
    intro b N
    by_cases hb : b ∈ bs
    · obtain ⟨n, hn, hle⟩ := hfreq b hb N
      exact ⟨n, hn, fun _ => hle⟩
    · exact ⟨N, le_refl N, fun hcon => absurd hcon hb⟩
  choose ν hνle hνsep using hpick
  set blocks : ℕ → List (UnitaryBlock G) := fun k =>
    bs.toList.map (fun b => ⟨A.model (ν b k), fun g => A.map (ν b k) g⟩) with hblocks
  have hmem : ∀ (b : G) (k : ℕ), b ∈ bs →
      (⟨A.model (ν b k), fun g => A.map (ν b k) g⟩ : UnitaryBlock G)
        ∈ blocks k := by
    intro b k hb
    rw [hblocks]
    exact List.mem_map_of_mem (Finset.mem_toList.mpr hb)
  have hnonempty : ∀ k : ℕ, 0 < Fintype.card (blockListModel (blocks k)) := by
    intro k
    obtain ⟨b, hb⟩ := hbs
    exact card_blockListModel_pos_of_mem (hmem b k hb) (A.modelNonempty _)
  refine ⟨{
    model := fun k => blockListModel (blocks k)
    modelNonempty := hnonempty
    map := fun k g => blockListUnitary (blocks k) g
    asymptoticallyMultiplicative := ?_ },
    bs.inf' hbs c, ?_, ?_⟩
  · -- the defect of a block diagonal is the maximum of the coordinate defects
    intro g h ε hε
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    refine ⟨N, fun k hk => ?_⟩
    refine norm_blockListMap_mul_sub_le G (blocks k) g h hε.le ?_
    intro B hB
    rw [hblocks, List.mem_map] at hB
    obtain ⟨b, -, rfl⟩ := hB
    exact hN _ (le_trans hk (hνle b k))
  · -- the tolerance is positive
    rw [Finset.lt_inf'_iff]
    exact hc
  · -- every tested element keeps its own block at every stage
    intro b hb k
    refine le_trans (Finset.inf'_le c hb) ?_
    refine le_trans (hνsep b k hb) ?_
    exact norm_blockListMap_sub_one_ge_of_mem (hmem b k hb) b

/-! ## Theorem 7.2: the corrected multi-mover removal of condition (iii) -/

/-- **Theorem 7.2.**  If the analytic core kills every almost representation
that separates a prescribed finite set uniformly at every stage, the group is
not MF.  No single designated element is needed: Lemma 7.1 converts the
`limsup` separation supplied by an injective corona representation into the
stagewise separation the core consumes, simultaneously for the whole finite
set.

The hypothesis `hkill` is the analytic input of Section 7.2; the statement is
otherwise unconditional. -/
theorem not_isOperatorMF_of_no_multiMarked (bs : Finset G)
    (hbs : ∀ b ∈ bs, b ≠ 1)
    (hkill : ∀ (A : OpAlmostRepresentation G) (η : ℝ), 0 < η →
      (∀ b ∈ bs, ∀ k : ℕ,
        η ≤ ‖(A.map k b : Matrix (A.model k) (A.model k) ℂ) - 1‖) → False) :
    ¬ IsOperatorMF G := by
  classical
  rintro ⟨X, hX, rho, hrho⟩
  choose lift hlift using fun g : G => QuotientGroup.mk_surjective (rho g)
  have hmul := normMatrixCorona_lift_eventually_multiplicative X rho lift hlift
  set A : OpAlmostRepresentation G :=
    { model := X
      modelNonempty := hX
      map := fun n g => lift g n
      asymptoticallyMultiplicative := by
        intro g h ε hε
        have hev := hmul g h ε hε
        rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
        exact hev } with hA
  -- the lift of the identity is asymptotically the identity
  have hnull1 : lift 1 ∈ nullCofiniteOpSubgroup X := by
    rw [← QuotientGroup.eq_one_iff, hlift 1, map_one]
  -- every tested element is frequently separated from the identity lift
  have hsepex : ∀ b : G, ∃ δ : ℝ, 0 < δ ∧ (b ∈ bs →
      ∃ᶠ n in Filter.cofinite,
        δ ≤ ‖(lift b n : Matrix (X n) (X n) ℂ) - lift 1 n‖) := by
    intro b
    by_cases hb : b ∈ bs
    · have hbne : rho b ≠ 1 := by
        intro hcon
        exact hbs b hb (hrho (by simpa using hcon))
      obtain ⟨δ, hδ, hfr⟩ :=
        normMatrixCorona_lift_frequently_marked_separated X rho lift hlift hbne
      exact ⟨δ, hδ, fun _ => hfr⟩
    · exact ⟨1, one_pos, fun hcon => absurd hcon hb⟩
  choose δ hδpos hδfreq using hsepex
  -- hence frequently separated from the identity matrix
  have hfreq : ∀ b ∈ bs, ∀ N : ℕ, ∃ n, N ≤ n ∧
      δ b / 2 ≤ ‖(A.map n b : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
    intro b hb N
    have hev : ∀ᶠ n in Filter.cofinite, opLength (X n) (lift 1 n) < δ b / 2 :=
      hnull1 (δ b / 2) (half_pos (hδpos b))
    have hfr := (hδfreq b hb).and_eventually hev
    rw [Nat.cofinite_eq_atTop, Filter.frequently_atTop] at hfr
    obtain ⟨n, hn, hsep, hsmall⟩ := hfr N
    refine ⟨n, hn, ?_⟩
    show δ b / 2 ≤ ‖(lift b n : Matrix (X n) (X n) ℂ) - 1‖
    rw [opLength] at hsmall
    have htri : ‖(lift b n : Matrix (X n) (X n) ℂ) - lift 1 n‖
        ≤ ‖(lift b n : Matrix (X n) (X n) ℂ) - 1‖
          + ‖(1 : Matrix (X n) (X n) ℂ) - lift 1 n‖ := by
      have hsum := norm_sub_le ((lift b n : Matrix (X n) (X n) ℂ) - 1)
        ((lift 1 n : Matrix (X n) (X n) ℂ) - 1)
      have hcancel : (lift b n : Matrix (X n) (X n) ℂ) - 1
          - ((lift 1 n : Matrix (X n) (X n) ℂ) - 1)
          = (lift b n : Matrix (X n) (X n) ℂ) - lift 1 n := by abel
      rw [hcancel] at hsum
      have hrev : ‖(lift 1 n : Matrix (X n) (X n) ℂ) - 1‖
          = ‖(1 : Matrix (X n) (X n) ℂ) - lift 1 n‖ := norm_sub_rev _ _
      rw [hrev] at hsum
      exact hsum
    have hrev : ‖(1 : Matrix (X n) (X n) ℂ) - lift 1 n‖
        = ‖(lift 1 n : Matrix (X n) (X n) ℂ) - 1‖ := norm_sub_rev _ _
    rw [hrev] at htri
    linarith
  -- Lemma 7.1 upgrades this to stagewise separation, which the core kills
  obtain ⟨A', η, hη, hsepA'⟩ :=
    exists_stagewise_separated A bs (fun b => δ b / 2)
      (fun b _ => half_pos (hδpos b)) hfreq
  exact hkill A' η hη hsepA'

end BlockAmplification

end GroupApproximation
