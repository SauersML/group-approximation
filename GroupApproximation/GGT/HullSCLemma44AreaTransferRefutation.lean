import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric
import GroupApproximation.Algebra.HyperbolicFreeGroup
import GroupApproximation.Algebra.HyperbolicInteger
import GroupApproximation.Meta.AxiomGuard

/-!
# The unbounded relative-area transfer is false

The free group on two generators surjects onto the integer square grid.
Taking every quotient-null basis word as a relator gives relative area at
most one for every nonempty null word, and empty peripheral-letter support.
The image basis has the Manhattan metric and fails every four-point bound.
Thus `RelativeLinearAreaTransferStatement` cannot omit bounded relator lengths.
The original proposition is retained; see issue #201.
-/

namespace GroupApproximation.HullSC.AreaTransferRefutation

open WordMetric Hyperbolic

abbrev Grid := Multiplicative ℤ × Multiplicative ℤ

def axis (b : Bool) : Multiplicative ℤ →* Grid where
  toFun x := if b then (1, x) else (x, 1)
  map_one' := by cases b <;> rfl
  map_mul' x y := by cases b <;> rfl

def unitStep : Multiplicative ℤ := Multiplicative.ofAdd (1 : ℤ)

def quotient : FreeGroup Bool →* Grid :=
  FreeGroup.lift (fun b => axis b unitStep)

theorem quotient_surjective : Function.Surjective quotient := by
  rintro ⟨x, y⟩
  refine ⟨FreeGroup.of false ^ x.toAdd * FreeGroup.of true ^ y.toAdd, ?_⟩
  apply Prod.ext <;> apply Multiplicative.ext <;>
    simp [quotient, axis, unitStep, toAdd_zpow]

def gridAlphabet : Set Grid := quotient '' freeAlphabet Bool

theorem gridAlphabet_generates : IsSymmetricGeneratingSet gridAlphabet :=
  isSymmetricGeneratingSet_image quotient quotient_surjective
    isSymmetricGeneratingSet_freeAlphabet

def manhattan (g : Grid) : ℕ := g.1.toAdd.natAbs + g.2.toAdd.natAbs

theorem manhattan_mul_le (g h : Grid) :
    manhattan (g * h) ≤ manhattan g + manhattan h := by
  have h₁ := Int.natAbs_add_le g.1.toAdd h.1.toAdd
  have h₂ := Int.natAbs_add_le g.2.toAdd h.2.toAdd
  simp only [manhattan, Prod.fst_mul, Prod.snd_mul, toAdd_mul]
  omega

theorem manhattan_letter {g : Grid} (hg : g ∈ gridAlphabet) :
    manhattan g = 1 := by
  obtain ⟨x, ⟨⟨b, sign⟩, rfl⟩, rfl⟩ := hg
  cases b <;> cases sign <;>
    norm_num [letterOf, quotient, axis, unitStep, manhattan]

theorem manhattan_prod_le (l : List Grid)
    (hl : ∀ g ∈ l, g ∈ gridAlphabet) : manhattan l.prod ≤ l.length := by
  induction l with
  | nil => simp [manhattan]
  | cons g l ih =>
      have hg := manhattan_letter (hl g (by simp))
      have ht := ih (fun x hx => hl x (by simp [hx]))
      have hm := manhattan_mul_le g l.prod
      simp only [List.prod_cons, List.length_cons]
      omega

theorem axis_intAlphabet_subset (b : Bool) :
    axis b '' intAlphabet ⊆ gridAlphabet := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · subst x
    refine ⟨FreeGroup.of b, letterOf_mem (b, true), ?_⟩
    simp [quotient, unitStep]
  · have hx' : x = Multiplicative.ofAdd (-1 : ℤ) := hx
    subst x
    refine ⟨(FreeGroup.of b)⁻¹, letterOf_mem (b, false), ?_⟩
    cases b <;> simp [quotient, axis, unitStep]

theorem wordNorm_axis_le (b : Bool) (x : Multiplicative ℤ) :
    wordNorm gridAlphabet (axis b x) ≤ x.toAdd.natAbs := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq isSymmetricGeneratingSet_intAlphabet x
  have hm := isWord_map (axis b) hl
  have hg : IsWord gridAlphabet (l.map (axis b)) (axis b x) :=
    ⟨fun g hg => axis_intAlphabet_subset b (hm.letters g hg), hm.prod_eq⟩
  have hbound := wordNorm_le_length hg
  rw [List.length_map, hlen, wordNorm_intAlphabet] at hbound
  exact hbound

theorem wordNorm_grid (g : Grid) : wordNorm gridAlphabet g = manhattan g := by
  apply le_antisymm
  · have hx := wordNorm_axis_le false g.1
    have hy := wordNorm_axis_le true g.2
    have hm := wordNorm_mul_le gridAlphabet_generates
      (axis false g.1) (axis true g.2)
    have heq : axis false g.1 * axis true g.2 = g := by
      simp [axis]
    rw [heq] at hm
    unfold manhattan
    omega
  · obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq gridAlphabet_generates g
    have hbound := manhattan_prod_le l hl.letters
    rwa [hl.prod_eq, hlen] at hbound

theorem wordDist_grid (g h : Grid) :
    wordDist gridAlphabet g h =
      (-g.1.toAdd + h.1.toAdd).natAbs + (-g.2.toAdd + h.2.toAdd).natAbs := by
  change wordNorm gridAlphabet (g⁻¹ * h) = _
  rw [wordNorm_grid]
  simp [manhattan]

theorem grid_not_fourPoint (δ : ℕ) :
    ¬ IsFourPointHyperbolic gridAlphabet δ := by
  intro h
  let n : ℤ := δ + 1
  have hs := h (1, 1)
    (Multiplicative.ofAdd n, Multiplicative.ofAdd n)
    (Multiplicative.ofAdd n, 1) (1, Multiplicative.ofAdd n)
  simp only [wordDist_grid, toAdd_one, toAdd_ofAdd, neg_zero, zero_add,
    neg_add_cancel, add_zero, Int.natAbs_zero, zero_add] at hs
  simp only [Int.natAbs_neg] at hs
  have hn : n.natAbs = δ + 1 := by dsimp [n]; omega
  rw [hn] at hs
  omega

def source : GGT.RelGenSet (FreeGroup Bool) Empty where
  base := freeAlphabet Bool
  fam := Empty.elim
  symmetricGenerating := by
    simpa using (isSymmetricGeneratingSet_freeAlphabet (α := Bool))

theorem source_alphabet : source.alphabet.carrier = freeAlphabet Bool := by
  simp [source, GGT.RelGenSet.alphabet]

theorem source_embedded : source.IsHyperbolicallyEmbedded := by
  refine ⟨⟨0, ?_⟩, fun i => i.elim⟩
  have hfour : IsFourPointHyperbolic source.alphabet.carrier 0 := by
    rw [source_alphabet]
    exact isFourPointHyperbolic_zero_of_isTreeLike
      isSymmetricGeneratingSet_freeAlphabet isTreeLike_freeAlphabet
  simpa only [Nat.cast_zero] using
    GGT.isHyperbolicSpace_cayley_of_fourPoint source.alphabet hfour

def kernelRelators : Set (List (GGT.RelLetter (FreeGroup Bool) Empty)) :=
  {w | ∃ l : List (FreeGroup Bool),
    (∀ x ∈ l, x ∈ freeAlphabet Bool) ∧ quotient l.prod = 1 ∧
      w = l.map GGT.RelLetter.base}

theorem kernelRelators_admissible :
    ∀ w ∈ kernelRelators, RelWord.IsAdmissible source w := by
  rintro w ⟨l, hl, _, rfl⟩ a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact hl x hx

theorem kernelRelators_killed :
    ∀ w ∈ kernelRelators, quotient (GGT.RelLetter.listVal w) = 1 := by
  rintro w ⟨l, _, hq, rfl⟩
  simpa [GGT.RelLetter.listVal, List.map_map, Function.comp_def,
    GGT.RelLetter.val] using hq

theorem kernelRelators_support :
    {a : GGT.RelLetter (FreeGroup Bool) Empty |
      (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
        ∃ w ∈ kernelRelators, a ∈ w}.Finite := by
  apply Set.finite_empty.subset
  rintro a ⟨⟨i, _, _⟩, _⟩
  exact i.elim

theorem kernelRelators_linearArea :
    RelativeLinearKernelArea source kernelRelators quotient := by
  intro l hl hq
  cases l with
  | nil => exact ⟨0, le_rfl, RelatorDefectBudget.IsRelatorProduct.one⟩
  | cons x l =>
      refine ⟨1, by simp, RelatorDefectBudget.IsRelatorProduct.base ?_⟩
      refine ⟨(x :: l).map GGT.RelLetter.base, ?_, ?_⟩
      · refine ⟨x :: l, ?_, hq, rfl⟩
        simpa [source_alphabet] using hl.letters
      · simp [GGT.RelLetter.listVal, List.map_map, Function.comp_def,
          GGT.RelLetter.val]

theorem kernelRelators_normalClosure :
    quotient.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' kernelRelators) :=
  kernelRelators_linearArea.ker_eq_normalClosure kernelRelators_killed

end AreaTransferRefutation

theorem not_relativeLinearAreaTransferStatement :
    ¬ RelativeLinearAreaTransferStatement.{0, 0, 0} := by
  intro h
  obtain ⟨C⟩ := h AreaTransferRefutation.source
    AreaTransferRefutation.source_embedded AreaTransferRefutation.kernelRelators
    AreaTransferRefutation.quotient AreaTransferRefutation.quotient_surjective
    AreaTransferRefutation.kernelRelators_support
    AreaTransferRefutation.kernelRelators_linearArea
  have hfour := C.fourPoint
  rw [GGT.RelGenSet.alphabet_carrier_mapSurjective,
    AreaTransferRefutation.source_alphabet] at hfour
  exact AreaTransferRefutation.grid_not_fourPoint C.delta hfour

end GroupApproximation.HullSC

#audit_closed_axioms GroupApproximation.HullSC.not_relativeLinearAreaTransferStatement
