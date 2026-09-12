import GroupApproximation.KunThom.CentralizerBisectionRepresentationScaled

/-!
# The patched bisection against the permutation it represents

Forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), finite form, on a
`ScaledPartialClusterSystem` placed disjointly in a model `Y`.  Let `b` complete the
selected arrows of a permutation `q` (`exists_bisection_selected`), and suppose the block
actions have tagged expansion at a fixed level `c > 0` and scale `1`.

`mul_card_hammingDisagreement_scaledBisectionPatch_le` bounds `c² h` times the Hamming
disagreement of `scaledBisectionArrows b` with `q` by
* `c² h` times the uncovered mass;
* `(c² h + 2 c h)` times the threshold total `h |Y| / 36`;
* `2 h` times `|L|` piece charges and `c` obstructions of `q`;
* `c` times the exceptional mass bound of `mul_sum_card_model_le_of_not_selected` at
  `K = 38`.

The retained objects are the selected objects whose re-separation scale
`separationScale` is at most half of the object.  Every other selected object is at most
twice its scale, and the objects that are not selected are exceptional.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection CategoryTheory

universe u

variable {Y : FiniteModel} {I : Type u}

section Scaled

variable [Fintype I] {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
variable (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
  (hinj : ∀ X, Function.Injective (ι X))
  (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')

/-- The re-separation scale of an object: the defects of its representative arrow and of
its bridge, divided by the expansion level. -/
noncomputable def separationScale (q : Equiv.Perm Y)
    (b : FiniteGroupoid.Bisection D.presentation.Obj) (c : ℝ) (X : I) : ℝ :=
  (((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X).equivarianceDefect
      (D.act X) (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) +
    ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ)) / c

theorem separationScale_nonneg (q : Equiv.Perm Y)
    (b : FiniteGroupoid.Bisection D.presentation.Obj) {c : ℝ} (hc : 0 ≤ c) (X : I) :
    0 ≤ separationScale D ι hinj hdisj q b c X :=
  div_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hc

theorem mul_separationScale (q : Equiv.Perm Y)
    (b : FiniteGroupoid.Bisection D.presentation.Obj) {c : ℝ} (hc : 0 < c) (X : I) :
    c * separationScale D ι hinj hdisj q b c X =
      ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X).equivarianceDefect
        (D.act X) (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) +
      ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) := by
  unfold separationScale
  have hcne : c ≠ 0 := hc.ne'
  field_simp

/-- **The patched bisection against `q`.** -/
theorem mul_card_hammingDisagreement_scaledBisectionPatch_le [DecidableEq I]
    (act : L → Equiv.Perm Y) (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (hb : ∀ X (hX : X ∈ selectedObjects D ι hinj hdisj q),
      ∃ e : b.objEquiv X = selectedObjectTarget D ι hinj hdisj q X,
        b.hom X ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX)
    {c : ℝ} (hc : 0 < c) (hexp : ∀ X, HasTaggedExpansionAtScale (D.act X) c 1) :
    c * c * D.h * ((hammingDisagreement
      (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).patch q).card : ℝ) ≤
      c * c * D.h * ((scaledClusterEmbedding D.clusterData ι hinj hdisj).uncovered.card : ℝ) +
        (c * c * D.h + 2 * c * D.h) * (D.h / 36 * Fintype.card Y) +
        2 * D.h * (Fintype.card L * ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj
            act D.act).pieceCharge q c X +
          c * ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).obstructionMass q X) +
        c * ((D.h + 38 * (D.h + 2 * Fintype.card L)) *
            ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
              D.act).pieceCharge q c X +
          (2 * D.h + 38 * (D.h + 2 * Fintype.card L)) *
            ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
              D.act).pieceCharge q⁻¹ c X +
          2 * 38 * c * (∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
              D.act).obstructionMass q X +
            ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
              D.act).obstructionMass q⁻¹ X)) := by
  classical
  have hc0 : 0 ≤ c := hc.le
  have hh : 0 ≤ D.h := D.h_pos.le
  -- the selected indices, the retained ones and the others
  let sel : Finset I := Finset.univ.filter fun X ↦
    (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q
  let good : Finset I := sel.filter fun X ↦
    2 * separationScale D ι hinj hdisj q b c X ≤ Fintype.card (D.model X)
  let bad : Finset I := sel.filter fun X ↦
    ¬ 2 * separationScale D ι hinj hdisj q b c X ≤ Fintype.card (D.model X)
  let unsel : Finset I := Finset.univ.filter fun X ↦
    (⟨X⟩ : D.presentation.Obj) ∉ selectedObjects D ι hinj hdisj q
  have hsel : ∀ X ∈ sel, (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q :=
    fun X hX ↦ (Finset.mem_filter.mp hX).2
  have hgood : ∀ X ∈ good, X ∈ sel ∧
      2 * separationScale D ι hinj hdisj q b c X ≤ Fintype.card (D.model X) :=
    fun X hX ↦ Finset.mem_filter.mp hX
  -- the retained re-separation
  have H0 := card_hammingDisagreement_scaledBisectionPatch_le D ι hinj hdisj q b good hexp
    (separationScale D ι hinj hdisj q b c)
    (fun X _ ↦ separationScale_nonneg D ι hinj hdisj q b hc0 X)
    (fun X _ ↦ by
      have hlt := Nat.lt_floor_add_one (separationScale D ι hinj hdisj q b c X)
      have hmul := mul_lt_mul_of_pos_left hlt hc
      have hcx := mul_separationScale D ι hinj hdisj q b hc X
      push_cast
      linarith)
    (fun X hX ↦ near_bridge_of_selected D ι hinj hdisj q b hb (hsel X (hgood X hX).1))
    (fun X hX ↦ by
      have hP := (hgood X hX).2
      have hx0 := separationScale_nonneg D ι hinj hdisj q b hc0 X
      have hfl : (⌊separationScale D ι hinj hdisj q b c X⌋₊ : ℝ) ≤
          separationScale D ι hinj hdisj q b c X := Nat.floor_le hx0
      have hnat : 2 * ⌊separationScale D ι hinj hdisj q b c X⌋₊ ≤ Fintype.card (D.model X) := by
        have hreal : ((2 * ⌊separationScale D ι hinj hdisj q b c X⌋₊ : ℕ) : ℝ) ≤
            (Fintype.card (D.model X) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast hreal
      have hsX := D.scale_eq X
      have hlX := D.scale_large X
      have hmin := min_le_left (D.scale X)
        (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X))
      omega)
  -- the glued domain
  have H1 := (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).card_compl_domain_le
  have H1' : ∑ X, ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
      ).sourceDefect ≤ ∑ X, (((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
        ).equivarianceDefect (D.act X)
          (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card :=
    Finset.sum_le_sum fun X _ ↦ sourceDefect_le_card_equivarianceDefect _ _ _
  have H1'' := sum_card_equivarianceDefect_scaledBisectionArrows_le D ι hinj hdisj b
  have H1c : ((Finset.univ \
      (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).domain).card : ℝ) ≤
      ((scaledClusterEmbedding D.clusterData ι hinj hdisj).uncovered.card : ℝ) +
        ∑ X, ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
          ).equivarianceDefect (D.act X)
            (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) := by
    have hnat := H1.trans (Nat.add_le_add_left H1' _)
    exact_mod_cast hnat
  -- the objects outside the retained ones
  have hcompl : goodᶜ ⊆ unsel ∪ bad := by
    intro X hX
    rw [Finset.mem_compl] at hX
    by_cases hs : (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, fun hP ↦ hX ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, hP⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  have hdisjUB : Disjoint unsel bad := by
    rw [Finset.disjoint_left]
    intro X hXu hXb
    exact (Finset.mem_filter.mp hXu).2 (hsel X (Finset.mem_filter.mp hXb).1)
  have H2a : ∑ X ∈ goodᶜ, (Fintype.card (D.model X) : ℝ) ≤
      ∑ X ∈ unsel, (Fintype.card (D.model X) : ℝ) +
        ∑ X ∈ bad, (Fintype.card (D.model X) : ℝ) := by
    rw [← Finset.sum_union hdisjUB]
    exact Finset.sum_le_sum_of_subset_of_nonneg hcompl fun _ _ _ ↦ Nat.cast_nonneg _
  have H2b : ∑ X ∈ bad, (Fintype.card (D.model X) : ℝ) ≤
      ∑ X ∈ bad, 2 * separationScale D ι hinj hdisj q b c X :=
    Finset.sum_le_sum fun X hX ↦ le_of_lt (not_le.mp (Finset.mem_filter.mp hX).2)
  have H2c : ∑ X ∈ good, separationScale D ι hinj hdisj q b c X +
      ∑ X ∈ bad, separationScale D ι hinj hdisj q b c X =
        ∑ X ∈ sel, separationScale D ι hinj hdisj q b c X :=
    Finset.sum_filter_add_sum_filter_not sel _ _
  have H2d : ∑ X ∈ bad, 2 * separationScale D ι hinj hdisj q b c X =
      2 * ∑ X ∈ bad, separationScale D ι hinj hdisj q b c X :=
    (Finset.mul_sum _ _ _).symm
  have H2e : 0 ≤ ∑ X ∈ good, separationScale D ι hinj hdisj q b c X :=
    Finset.sum_nonneg fun X _ ↦ separationScale_nonneg D ι hinj hdisj q b hc0 X
  -- the retained scales
  have H3 : c * ∑ X ∈ sel, separationScale D ι hinj hdisj q b c X ≤
      ∑ X, ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
          ).equivarianceDefect (D.act X)
            (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) +
        ∑ X ∈ sel, ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
            (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) := by
    rw [Finset.mul_sum]
    calc ∑ X ∈ sel, c * separationScale D ι hinj hdisj q b c X
        = ∑ X ∈ sel, (((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
            ).equivarianceDefect (D.act X)
              (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) +
            ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
              (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
                (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ)) :=
          Finset.sum_congr rfl fun X _ ↦ mul_separationScale D ι hinj hdisj q b hc X
      _ = ∑ X ∈ sel, ((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
            ).equivarianceDefect (D.act X)
              (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) +
          ∑ X ∈ sel, ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
            (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
              (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) :=
          Finset.sum_add_distrib
      _ ≤ _ :=
          add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun X _ _ ↦ Nat.cast_nonneg (α := ℝ)
              (((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
                ).equivarianceDefect (D.act X)
                  (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card) le_rfl
  -- the bridges at the selected objects
  have H4 : c * ∑ X ∈ sel, ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ) ≤
      Fintype.card L * ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
          D.act).pieceCharge q c X +
        c * ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
          D.act).obstructionMass q X := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ∑ X ∈ sel, c * ((((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
            (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℝ)
        ≤ ∑ X ∈ sel, (Fintype.card L * (scaledClusterAction (D := D.clusterData) ι hinj hdisj
            act D.act).pieceCharge q c X + c * (scaledClusterAction (D := D.clusterData) ι hinj
              hdisj act D.act).obstructionMass q X) :=
          Finset.sum_le_sum fun X hX ↦
            mul_card_equivarianceDefect_bridge_selected_le D ι hinj hdisj act q b hb hc0 hexp
              (hsel X hX)
      _ ≤ ∑ X, (Fintype.card L * (scaledClusterAction (D := D.clusterData) ι hinj hdisj
            act D.act).pieceCharge q c X + c * (scaledClusterAction (D := D.clusterData) ι hinj
              hdisj act D.act).obstructionMass q X) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun X _ _ ↦
            add_nonneg (mul_nonneg (Nat.cast_nonneg _)
              ((scaledClusterAction (D := D.clusterData) ι hinj hdisj act D.act).pieceCharge_nonneg
                q hc0 X))
              (mul_nonneg hc0 ((scaledClusterAction (D := D.clusterData) ι hinj hdisj act
                D.act).obstructionMass_nonneg q X))
  -- the objects that are not selected
  have H5 := (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
    D.act).mul_sum_card_model_le_of_not_selected q (fun X X' ↦ min (D.scale X) (D.scale X'))
      hc0 hh (by norm_num : (0 : ℝ) ≤ 38) hexp
      (fun C X hC _ ↦ card_model_le_of_two_mul_card_bridgeSource_scaled D ι hinj hdisj q
        (X := X) hC)
      unsel
      (fun C hC X' hcand ↦ (Finset.mem_filter.mp hC).2
        ((mem_selectedObjects D ι hinj hdisj q ⟨C⟩).mpr ⟨X', hcand⟩))
  have H5' : c * D.h * ∑ X ∈ unsel, (Fintype.card (D.model X) : ℝ) ≤
      (D.h + 38 * (D.h + 2 * Fintype.card L)) *
          ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).pieceCharge q c X +
        (2 * D.h + 38 * (D.h + 2 * Fintype.card L)) *
          ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).pieceCharge q⁻¹ c X +
        2 * 38 * c * (∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).obstructionMass q X +
          ∑ X, (scaledClusterAction (D := D.clusterData) ι hinj hdisj act
            D.act).obstructionMass q⁻¹ X) :=
    H5
  -- assembly
  have hch : 0 ≤ c * c * D.h := by positivity
  have p₀ := mul_le_mul_of_nonneg_left H0 hch
  have p₁ := mul_le_mul_of_nonneg_left H1c hch
  have p₂ := mul_le_mul_of_nonneg_left H2a hch
  have p₃ := mul_le_mul_of_nonneg_left (H2b.trans_eq H2d) hch
  have p₁₀ : c * c * D.h * (∑ X ∈ good, separationScale D ι hinj hdisj q b c X +
      ∑ X ∈ bad, separationScale D ι hinj hdisj q b c X) =
      c * c * D.h * ∑ X ∈ sel, separationScale D ι hinj hdisj q b c X := by
    rw [H2c]
  have p₄ := mul_le_mul_of_nonneg_left H3 (by positivity : (0 : ℝ) ≤ 2 * c * D.h)
  have p₅ := mul_le_mul_of_nonneg_left H4 (by positivity : (0 : ℝ) ≤ 2 * D.h)
  have p₆ := mul_le_mul_of_nonneg_left H5' hc0
  have p₇ := mul_le_mul_of_nonneg_left H1'' (by positivity : (0 : ℝ) ≤ c * c * D.h + 2 * c * D.h)
  have p₈ := mul_nonneg hch H2e
  have hselsum : 0 ≤ ∑ X ∈ bad, separationScale D ι hinj hdisj q b c X :=
    Finset.sum_nonneg fun X _ ↦ separationScale_nonneg D ι hinj hdisj q b hc0 X
  have p₉ := mul_nonneg hch hselsum
  linarith

end Scaled

end BlockPatching
end GroupApproximation
