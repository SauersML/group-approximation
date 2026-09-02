import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# The Lemma 62 unbound-budget constructor

This file isolates the geometric part of Osin's Appendix Lemma 62 from the
already proved averaging calculation.  A complementary-component partition
certificate gives the strict square-root bound on the selected unbound arcs;
the final numerical threshold is supplied separately at the parameter value
chosen by the estimating construction.  The source is Osin, Appendix Lemma
62, with the partition certificate corresponding to its complementary-disc
decomposition and averaging inequality.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate

universe u w v

/-! ## The strictly smaller Lemma 62 geometric estimate -/

/-- The square-root part of Osin's Appendix Lemma 62 after the finite
partition has been chosen.  The partition total is the sum of the component
lengths, and the component count is bounded by `53 * n`; the geometric work
of constructing such a certificate is kept outside this arithmetic
statement. -/
def UnboundLengthBudgetStatement : Prop :=
  ∀ {n d : ℕ} {t total : ℝ}
    (certificate : PartitionUnboundCertificate n d t total),
      total < (n : ℝ) * t

/-! ## Finite partition counting -/

/-- A finite family of pieces satisfies the sum bound obtained by summing the
pointwise density estimate.  This is the finite-partition use of
`Finset.sum_le_sum` in Osin's Appendix Lemma 62. -/
theorem finite_piece_sum_le_constant_mul
    {d : ℕ} (unbound piece : Fin d → ℝ) (constant : ℝ)
    (hcomponent : ∀ i : Fin d, unbound i ≤ constant * piece i) :
    (∑ i : Fin d, unbound i) ≤ constant * ∑ i : Fin d, piece i := by
  calc
    (∑ i : Fin d, unbound i) ≤ ∑ i : Fin d, constant * piece i := by
      apply Finset.sum_le_sum
      intro i _
      exact hcomponent i
    _ = constant * ∑ i : Fin d, piece i := by
      rw [Finset.mul_sum]

/-- A finite set of pieces is bounded by its cardinality times a common
constant.  The proof exposes the `Finset.card` bound used in the planar
counting argument. -/
theorem finset_piece_sum_le_of_card_bound
    {α : Type u} [DecidableEq α] {N : ℕ} (s : Finset α)
    (piece : α → ℝ) (bound : ℝ)
    (hpiece : ∀ i ∈ s, piece i ≤ bound)
    (hcard : s.card ≤ N) (hbound : 0 ≤ bound) :
    (∑ i ∈ s, piece i) ≤ (N : ℝ) * bound := by
  calc
    (∑ i ∈ s, piece i) ≤ ∑ i ∈ s, bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpiece i hi
    _ = (s.card : ℝ) * bound := by simp
    _ ≤ (N : ℝ) * bound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbound

/-- The unbound part of a partition is bounded by the sum of its piece
lengths times the `t / 60` density constant. -/
theorem partition_unbound_le_piece_sum
    {n d : ℕ} {t : ℝ}
    (averaging : Lemma62AveragingCertificate n d t) :
    (∑ i : Fin d, averaging.unboundLength i) ≤
      (t / 60) * ∑ i : Fin d, (averaging.arcCount i : ℝ) := by
  apply finite_piece_sum_le_constant_mul
  intro i
  calc
    averaging.unboundLength i ≤
        (averaging.arcCount i : ℝ) * t / 60 :=
      le_of_lt (averaging.component_lt i)
    _ = (t / 60) * (averaging.arcCount i : ℝ) := by ring

/-- Every partition certificate satisfies the strict `n * t` budget.  The
strict margin is the numerical inequality `53 / 60 < 1`, while the sum and
cardinality bounds are supplied by the two finite counting lemmas above. -/
theorem unboundLengthBudgetStatement : UnboundLengthBudgetStatement := by
  intro n d t total certificate
  rw [← certificate.total_eq]
  have hpiece := partition_unbound_le_piece_sum certificate.averaging
  have hcount :
      (∑ i : Fin d, (certificate.averaging.arcCount i : ℝ)) ≤
        53 * (n : ℝ) := by
    exact_mod_cast certificate.averaging.arc_count_le
  have hscaled :
      (t / 60) * ∑ i : Fin d,
          (certificate.averaging.arcCount i : ℝ) ≤
        (t / 60) * (53 * (n : ℝ)) := by
    have htNonneg : 0 ≤ t := le_of_lt certificate.averaging.t_pos
    exact mul_le_mul_of_nonneg_left hcount (div_nonneg htNonneg (by norm_num))
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast certificate.averaging.n_pos
  have ht : 0 < t := certificate.averaging.t_pos
  have hmargin : (t / 60) * (53 * (n : ℝ)) < (n : ℝ) * t := by
    nlinarith
  exact lt_of_le_of_lt (le_trans hpiece hscaled) hmargin

/-- The cardinality estimate has the exact empty-partition model: the piece
sum and its budget are both zero. -/
theorem finset_piece_sum_empty_model (bound : ℝ) (hbound : 0 ≤ bound) :
    (∑ i ∈ (Finset.univ : Finset (Fin 0)), (0 : ℝ)) ≤
      (0 : ℝ) * bound := by
  refine finset_piece_sum_le_of_card_bound (s := Finset.univ)
    (piece := fun _ : Fin 0 => (0 : ℝ)) (bound := bound) ?_ ?_ hbound
  · intro i hi
    norm_num
  · simp

/-- The cardinality estimate has the exact one-piece model: one piece of
length `bound` has budget `bound`. -/
theorem finset_piece_sum_oneCell_model (bound : ℝ) (hbound : 0 ≤ bound) :
    (∑ i ∈ (Finset.univ : Finset (Fin 1)), bound) ≤
      (1 : ℝ) * bound := by
  refine finset_piece_sum_le_of_card_bound (s := Finset.univ)
    (piece := fun _ : Fin 1 => bound) (bound := bound) ?_ ?_ hbound
  · intro i hi
    exact le_rfl
  · simp

/-- The empty-family partition certificate identifies its total by equality
with the empty finite sum, so its budget starts at exactly zero. -/
theorem unboundLengthBudget_emptyFamily_equality_model :
    ∃ certificate : PartitionUnboundCertificate 1 0 1 0,
      (∑ i : Fin 0, certificate.averaging.unboundLength i) = (0 : ℝ) := by
  obtain ⟨certificate⟩ := partitionUnboundCertificate_emptyModel
  exact ⟨certificate, certificate.total_eq⟩

/-- The one-cell partition model is an instance of the budget statement, with
the strict conclusion supplied by the positive parameter field of its
certificate. -/
theorem unboundLengthBudget_oneCell_model (t : ℝ) :
    ∀ {total : ℝ} (certificate : PartitionUnboundCertificate 1 1 t total),
      total < (1 : ℝ) * t := by
  intro total certificate
  simpa using unboundLengthBudgetStatement certificate

/-- A complementary-component averaging certificate is exactly sufficient for
the budget field of `Lemma62Data`.  The equality in the certificate fixes the
total to the canonical partition total of the selected scaffold. -/
theorem lemma62Data_of_partitionCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    {d : ℕ}
    (certificate : PartitionUnboundCertificate Delta.rCellCount d
      (Real.sqrt (rho : ℝ)) (scaffold.partition.unboundTotal : ℝ))
  (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  exact unboundLengthBudgetStatement certificate

/-- At parameters for which the square-root budget and the numerical
threshold are available, the full `Lemma62Data` object is constructed without
any further diagram argument. -/
theorem estimatingUnboundConstruction_at_of_lengthBudget
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu : ℝ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hbudget : (scaffold.partition.unboundTotal : ℝ) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  exact hbudget

/-! ## Degenerate models -/

/-- The empty-family model is vacuous in the positive-cell branch.  This
checks the budget interface against the same empty-family obstruction used by
the finite selection and deletion layers. -/
theorem unboundConstruction_emptyFamily_model
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (_hcondition : OsinCCondition D
      (∅ : Set (List (GGT.RelLetter G Lambda))) eps mu lambda c rho)
    (scaffold : EstimatingScaffold D eps Delta)
    (_hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  exact (no_positive_rCells_emptyFamily Delta hcells).elim

/-- In the one-cell model, vanishing unbound total gives the strict budget as
soon as `rho` is positive.  The remaining threshold is displayed explicitly,
so this model does not hide the large-`rho` numerical premise. -/
theorem lemma62Data_oneCell_zeroUnbound_model
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hrcell : Delta.rCellCount = 1)
    (hunbound : scaffold.partition.unboundTotal = 0)
    (hrho : 0 < rho)
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  refine ⟨{ unbound_lt := ?_, threshold := hthreshold }⟩
  rw [hunbound, hrcell, Nat.cast_one, one_mul]
  have hrhoReal : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hrho
  exact Real.sqrt_pos.2 hrhoReal

/-- The threshold field rules out `rho = 0` for every fixed diagram and
scaffold.  The universal estimating statement quantifies `rho` without a
positive-parameter premise, so this is the exact numerical obstruction to an
unconditional producer for that statement. -/
theorem no_lemma62Data_at_rho_zero
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta} :
    ¬ Nonempty (Lemma62Data D eps mu 0 Delta scaffold) := by
  rintro ⟨data⟩
  norm_num at data.threshold

/-- The averaging certificate has the exact empty-component model used by the
partition producer, and its numerical output is strict at the smallest
positive square-root parameter. -/
theorem partitionCertificate_empty_model_check :
    Nonempty (PartitionUnboundCertificate 1 0 1 0) :=
  partitionUnboundCertificate_emptyModel

end Estimating
end VanKampen
end GGT
end GroupApproximation
