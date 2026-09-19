import GroupApproximation.GGT.VanKampen.Estimating.ZeroConnectorObstruction
import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.VanKampen.Estimating.UnboundRepaired

/-!
# The unbound obstruction persists at small mu

The group is S₃ × ℤ with the full base alphabet. The two relators are the
1089-letter constant words in `a` and `a⁻¹`, and the singleton outer boundary
spells a conjugate of `a^1089` with a different permutation coordinate.
At epsilon zero only empty pieces occur. The parameters satisfy the source's
strict mu range and the displayed budget threshold, but not its geometric
scale requirements.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample

open GroupApproximation.HullSC GroupApproximation.WordMetric Embedded
open GroupApproximation.Manuscript.NonMF.TorsionFree

abbrev G := Equiv.Perm (Fin 3) × Multiplicative ℤ

def a : G := (Equiv.swap 0 1, Multiplicative.ofAdd 1)
def t : G := (Equiv.swap 1 2, 1)
def b : G := t * a ^ 1089 * t⁻¹

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

def word (g : G) : List (RelLetter G Empty) := List.replicate 1089 (.base g)
def outer : List (RelLetter G Empty) := [.base b]
def W : Set (List (RelLetter G Empty)) := {word a, word a⁻¹}

theorem exponent_a (n : ℕ) : ((a ^ n).2).toAdd = (n : ℤ) := by
  simp [a]

theorem exponent_inv_a (n : ℕ) : (((a⁻¹) ^ n).2).toAdd = -(n : ℤ) := by
  simp [a]

theorem exponent_b : b.2.toAdd = 1089 := by
  simp [b, t, a]

theorem b_ne_one : b ≠ 1 := by
  intro h
  have he := congrArg (fun g : G => g.2.toAdd) h
  rw [exponent_b] at he
  norm_num at he

theorem b_ne_a_pow : b ≠ a ^ 1089 := by
  intro h
  have hp := congrArg Prod.fst h
  have hpow : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ^ 1089 = Equiv.swap 0 1 := by
    rw [show (1089 : ℕ) = 2 * 544 + 1 by norm_num, pow_add, pow_mul]
    have hsquare : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ^ 2 = 1 := by decide
    rw [hsquare]
    simp
  have hd : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 *
      (Equiv.swap 1 2)⁻¹ ≠ Equiv.swap 0 1 := by decide
  change (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 ^ 1089 *
    (Equiv.swap 1 2)⁻¹ = Equiv.swap 0 1 ^ 1089 at hp
  rw [hpow] at hp
  exact hd hp

theorem prefix_value {g : G} {first suffix : List (RelLetter G Empty)}
    (hsplit : word g = first ++ suffix) :
    RelLetter.listVal first = g ^ first.length := by
  have hfirst := (List.replicate_eq_append_iff.mp hsplit).2.1
  conv_lhs => rw [hfirst]
  simp [RelLetter.listVal, RelLetter.val]

theorem prefix_length_le {g : G} {first suffix : List (RelLetter G Empty)}
    (hsplit : word g = first ++ suffix) : first.length ≤ 1089 := by
  have hlen := (List.replicate_eq_append_iff.mp hsplit).1
  omega

theorem prefix_values_avoid : ZeroConnectorObstruction.PrefixValuesAvoid W b := by
  intro relator hrelator first suffix hsplit hne
  have hpos : 0 < first.length := List.length_pos_iff.mpr hne
  rcases hrelator with hrelator | hrelator
  · rw [hrelator] at hsplit
    rw [prefix_value hsplit]
    constructor
    · intro h
      have he := congrArg (fun g : G => g.2.toAdd) h
      rw [exponent_a] at he
      change (first.length : ℤ) = 0 at he
      omega
    · intro h
      have he := congrArg (fun g : G => g.2.toAdd) h
      rw [exponent_a, exponent_b] at he
      have hn : first.length = 1089 := by omega
      rw [hn] at h
      exact b_ne_a_pow h.symm
  · have hr : relator = word a⁻¹ := Set.mem_singleton_iff.mp hrelator
    rw [hr] at hsplit
    rw [prefix_value hsplit]
    constructor
    · intro h
      have he := congrArg (fun g : G => g.2.toAdd) h
      rw [exponent_inv_a] at he
      change -(first.length : ℤ) = 0 at he
      omega
    · intro h
      have he := congrArg (fun g : G => g.2.toAdd) h
      rw [exponent_inv_a, exponent_b] at he
      omega

theorem quasiGeodesic_of_length_le {w : List (RelLetter G Empty)}
    (hlen : w.length ≤ 1089) : IsLambdaCQuasiGeodesicWord D 1 1089 w := by
  refine ⟨?_, ?_⟩
  · intro letter hletter
    cases letter with
    | base g => exact Set.mem_univ _
    | comp lam g => exact Empty.elim lam
  · intro i j hij hj
    have hlenReal : ((j - i : ℕ) : ℝ) ≤ 1089 := by
      exact_mod_cast (show j - i ≤ 1089 by omega)
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (wordDist D.alphabet.carrier (OsinComponents.vertex 1 w i) (OsinComponents.vertex 1 w j))
    linarith


theorem word_length (w : List (RelLetter G Empty)) (hw : w ∈ W) : w.length = 1089 := by
  rcases hw with rfl | hw
  · exact List.length_replicate ..
  · rw [Set.mem_singleton_iff.mp hw]
    exact List.length_replicate ..

theorem revInv_replicate (g : G) (n : ℕ) :
    RelWord.revInv (List.replicate n (RelLetter.base g : RelLetter G Empty)) =
      List.replicate n (RelLetter.base g⁻¹) := by
  simp [RelWord.revInv, RelWord.inv]

theorem publishedPiece_lengths_zero {first second relator : List (RelLetter G Empty)}
    (hpiece : RelWord.IsPublishedPiece D W 0 first second relator) :
    first.length = 0 ∧ second.length = 0 := by
  obtain ⟨hw, ⟨suffix, hs⟩, other, ho, suffix', hs', y, z, hy, hz, heq, hne⟩ := hpiece
  have hyOne : y = 1 :=
    (wordNorm_eq_zero_iff D.alphabet.symmetricGenerating y).mp (Nat.le_zero.mp hy)
  have hzOne : z = 1 :=
    (wordNorm_eq_zero_iff D.alphabet.symmetricGenerating z).mp (Nat.le_zero.mp hz)
  rw [hyOne, hzOne, one_mul, mul_one] at heq
  rw [hyOne, one_mul, inv_one, mul_one] at hne
  rcases hw with rfl | hw
  · rcases ho with rfl | ho
    · exact (hne rfl).elim
    · rw [Set.mem_singleton_iff.mp ho] at hs'
      rw [prefix_value hs, prefix_value hs'] at heq
      have he := congrArg (fun g : G => g.2.toAdd) heq
      rw [exponent_a, exponent_inv_a] at he
      omega
  · rw [Set.mem_singleton_iff.mp hw] at hs hne
    rcases ho with rfl | ho
    · rw [prefix_value hs, prefix_value hs'] at heq
      have he := congrArg (fun g : G => g.2.toAdd) heq
      rw [exponent_a, exponent_inv_a] at he
      omega
    · rw [Set.mem_singleton_iff.mp ho] at hne
      exact (hne rfl).elim

theorem condition : OsinCCondition D W 0 (1 / 32) 1 1089 1089 := by
  refine {
    admissible := ?_
    inv_mem := ?_
    rotate_mem := ?_
    long := ?_
    deep := ?_
    pieces_small := ?_
    quasiGeodesic := ?_
    publishedPiecesSmall := ?_ }
  · intro w hw
    exact (quasiGeodesic_of_length_le (le_of_eq (word_length w hw))).1
  · intro w hw
    rcases hw with rfl | hw
    · right
      exact revInv_replicate a 1089
    · rw [Set.mem_singleton_iff.mp hw]
      left
      change RelWord.revInv (List.replicate 1089 (RelLetter.base a⁻¹ : RelLetter G Empty)) = _
      rw [revInv_replicate, inv_inv]
      rfl
  · intro w hw n
    rcases hw with rfl | hw
    · left
      exact List.rotate_replicate _ _ _
    · right
      rw [Set.mem_singleton_iff.mp hw]
      exact List.rotate_replicate _ _ _
  · intro w hw
    exact le_of_eq (word_length w hw).symm
  · intro w hw letter hletter lam
    exact Empty.elim lam
  · intro first w hp
    obtain ⟨hw, hs, other, ho, _, second, suffix, hsplit, y, z, hy, hz, heq, hne⟩ := hp
    have hp' : RelWord.IsPublishedPiece D W 0 first second w :=
      ⟨hw, hs, other, ho, suffix, hsplit, y, z, hy, hz, heq, hne⟩
    rw [(publishedPiece_lengths_zero hp').1, word_length w hw]
    norm_num
  · intro w hw
    exact quasiGeodesic_of_length_le (le_of_eq (word_length w hw))
  · intro first second w hp
    have hw := hp.1
    obtain ⟨hfirst, hsecond⟩ := publishedPiece_lengths_zero hp
    rw [hfirst, hsecond, word_length w hw]
    norm_num

/-- The ambient Cayley metric also satisfies the missing hyperbolicity
hypothesis: every group element is a base letter. -/
theorem hyperbolic : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier 1 := by
  apply Hyperbolic.isFourPointHyperbolic_of_bounded
  intro x y
  apply wordNorm_le_one_of_mem
  exact Or.inl (Set.mem_univ _)

/-- The obstruction is inside the source's strict numerical ranges. -/
theorem valid_parameters :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1089 ∧
      (0 : ℝ) < 1 / 32 ∧ (1 / 32 : ℝ) < 1 / 16 ∧
      (1 : ℝ) ≤ 2 * (1 / 32) * Real.sqrt (1089 : ℝ) ∧
      (1 / (1 / 32) ^ 2 : ℝ) < 1089 := by
  norm_num


theorem word_value (g : G) : RelLetter.listVal (word g) = g ^ 1089 := by
  have h (n : ℕ) : RelLetter.listVal (List.replicate n (RelLetter.base g : RelLetter G Empty)) =
      g ^ n := by simp [RelLetter.listVal, RelLetter.val]
  exact h 1089

def algebraicCell : Lemma44OrientedRelatorCell W where
  relator := word a
  relator_mem := Or.inl rfl
  conjugator := t

def Z : RelativeReducedDiagram D W 1 where
  boundaryWord := [b]
  boundary := b
  boundary_ne_one := b_ne_one
  boundaryWord_isWord := ⟨by intro x hx; exact Or.inl (Set.mem_univ _), by simp⟩
  boundary_length_le := by decide
  area := 1
  area_pos := by decide
  cells := [algebraicCell]
  cells_length := rfl
  cell_values_prod := by
    change (t * RelLetter.listVal (word a) * t⁻¹) * 1 = b
    rw [word_value, mul_one]
    rfl
  no_cancelling_pair := by
    intro pre between suf first second hsplit
    have hlen := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  cell_relator_ne_nil := by
    rintro ⟨i, hi⟩
    change i < 1 at hi
    have hi0 : i = 0 := by omega
    subst i
    change word a ≠ []
    intro he
    have hlen := congrArg List.length he
    have hwlen := word_length (word a) (Or.inl rfl)
    rw [hwlen, List.length_nil] at hlen
    omega

theorem no_contiguity {Delta : DiscDiagram.{0, 0, 0} W}
    (hcount : Delta.rCellCount = 1) (hboundary : Delta.boundaryWord = outer)
    {faces : Finset Delta.toCombMap.Face} (Gamma : Contiguity D 0 Delta faces) : False :=
  ZeroConnectorObstruction.no_contiguity hcount hboundary b_ne_one
    condition.rotate_mem prefix_values_avoid Gamma

/-- An explicit valid input for which every O-equivalent output fails the
strict budget. The parameter and hyperbolicity checks above are independent
closed theorems, so adding those hypotheses does not remove this model. -/
theorem exists_counterexample :
    ∃ Delta : DiscDiagram.{0, 0, 0} W,
      Delta.Reduced ∧ Delta.rCellCount = 1 ∧ Delta.boundaryWord = outer ∧
      ∃ scaffold : EstimatingScaffold D 0 Delta,
        Nonempty (EstimatingGraphData D 0 Delta scaffold) ∧
        ∀ Delta' : DiscDiagram.{0, 0, 0} W,
          OEquivalentDiscDiagram Delta Delta' →
            ∀ scaffold' : EstimatingScaffold D 0 Delta',
              ¬ Nonempty (Lemma62Data D 0 (1 / 32) 1089 Delta' scaffold') := by
  obtain ⟨realization⟩ := relativeDiscRealizationSpellingStatement D W 1 Z outer rfl
  have hcount : realization.diagram.rCellCount = 1 := by
    have hc := Fintype.card_congr realization.cellIndex
    change Fintype.card (Fin 1) = Fintype.card (Fin realization.diagram.rCellCount) at hc
    simpa only [Fintype.card_fin] using hc.symm
  have hb := realization.outerWord_eq
  obtain ⟨scaffold⟩ := exists_estimatingScaffold D 0 realization.diagram
  have hempty := ZeroConnectorObstruction.selected_eq_empty (no_contiguity hcount hb) scaffold
  obtain ⟨graph⟩ := estimatingGraphData_emptyFamilyModel D 0 realization.diagram scaffold hempty
  refine ⟨realization.diagram, realization.reduced, hcount, hb, scaffold, ⟨graph⟩, ?_⟩
  intro Delta' equiv scaffold' hbudget
  obtain ⟨budget⟩ := hbudget
  have hc : Delta'.rCellCount = 1 := equiv.rCellCount_eq.trans hcount
  have hb' : Delta'.boundaryWord = outer := equiv.boundaryWord_eq.trans hb
  have hunbound : scaffold'.partition.unboundTotal = 1089 :=
    ZeroConnectorObstruction.unboundTotal_eq_cellLength hc
      (fun i => word_length _ (cell Delta' i).word_mem)
      (no_contiguity hc hb') scaffold'
  have hlt := budget.unbound_lt
  rw [hunbound, hc] at hlt
  norm_num at hlt

theorem not_estimatingUnboundOutputStatement :
    ¬ EstimatingUnboundOutputStatement.{0, 0, 0} := by
  intro h
  obtain ⟨Delta, hred, hcount, hb, scaffold, ⟨graph⟩, hbad⟩ := exists_counterexample
  obtain ⟨Delta', ⟨equiv⟩, _, scaffold', _, budget⟩ :=
    h D 0 1089 (1 / 32) 1 1089 (by norm_num) condition Delta hred (by omega)
      scaffold graph (by rw [hb]; exact quasiGeodesic_of_length_le (by decide))
  exact hbad Delta' equiv scaffold' budget

theorem not_estimatingUnboundRepairedStatement :
    ¬ EstimatingUnboundRepairedStatement.{0, 0, 0} :=
  fun h => not_estimatingUnboundOutputStatement (estimatingUnboundOutput_of_repaired h)

theorem not_lemma62ComponentPartitionStatement :
    ¬ Lemma62ComponentPartitionStatement.{0, 0, 0} :=
  fun h => not_estimatingUnboundRepairedStatement (estimatingUnboundRepaired_of_componentPartition h)

end GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.condition
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.hyperbolic
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.valid_parameters
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.exists_counterexample
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.not_estimatingUnboundOutputStatement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.not_estimatingUnboundRepairedStatement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample.not_lemma62ComponentPartitionStatement
