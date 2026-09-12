import GroupApproximation.KunThom.ComponentCountingNormalizationMedian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kun–Thom Lemma 4.4 in vertex form: objects to vertices and back

Kun and Thom (arXiv:2608.06222v3, Lemma 4.4) amplify one-sided inequalities
between the orbit sizes, or the isotropy orders, of matched cluster objects into
ratios tending to `1` in component-weight measure.  Hypotheses and conclusion
are statements about objects.  Median amplification
(`ComponentCountingNormalization.deviation_negligible` and `drop_negligible`) is
a statement about vertices.  This file carries the statements across.

Objects are presented by a vertex map `obj : Y → I`: the object `i` consists of
the vertices `y` with `obj y = i`, and the weight of a family `J` of objects is
the number of vertices in `objectVertices obj J`.  A matching of objects under a
permutation `p` of the vertices is a map `π : I → I` together with its domain
`Dom`.

* `drift_of_not_mem_vertexExceptional`: an inequality `f (π i) ≤ f i + κ` on the
  matched objects outside `Bad` is an inequality for `f ∘ obj` along `p` off the
  vertex exceptional set.  `card_vertexExceptional_le` bounds that set by the
  weight outside `Dom`, the weight of `Bad` and the matching leak.
* `card_objectVertices_failing_le`: the weight of the matched objects whose
  observable changes by more than `δ` is at most the vertex drop set of `f ∘ obj`
  along `p` plus the matching leak.
* The logarithmic observable `logObservable f i = log (max (f i) 1)` of a
  natural observable has a median on every block (`isMedian_logCut_natMedian`).
  A multiplicative inequality `(1 - ζ) a ≤ b` is an additive drift of at most
  `2ζ` (`logCut_le_add_of_mul_le`), and a bounded logarithmic change bounds the
  ratio (`le_exp_mul_of_abs_logCut_sub_le`).
* Label estimates for `deviation_negligible`: invariance off a negligible set
  (`clampedLabel_negligible_of_eqOff`), one-sided drift off a negligible set
  (`clampedLabel_negligible_of_oneSided`) and approximate inverses
  (`clampedLabel_negligible_inv`).
* `failingWeight_negligible`: once every ambient label moves the clamped
  logarithmic observable by a negligible amount, the matched objects along a
  rarely crossing permutation whose logarithmic observable changes by more than
  `2M` have negligible weight.
-/

namespace GroupApproximation
namespace MedianVertexForm

open scoped BigOperators
open ComponentCountingNormalization

/-! ### Objects presented by a vertex map -/

section Finite

variable {Y : FiniteModel} {I : Type*}

/-- The vertices of the objects in `J`. -/
def objectVertices [DecidableEq I] (obj : Y → I) (J : Finset I) : Finset Y :=
  Finset.univ.filter fun y ↦ obj y ∈ J

theorem mem_objectVertices [DecidableEq I] (obj : Y → I) (J : Finset I) (y : Y) :
    y ∈ objectVertices obj J ↔ obj y ∈ J := by
  simp only [objectVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The vertices outside the objects in `J`. -/
def outsideVertices [DecidableEq I] (obj : Y → I) (J : Finset I) : Finset Y :=
  Finset.univ.filter fun y ↦ obj y ∉ J

theorem mem_outsideVertices [DecidableEq I] (obj : Y → I) (J : Finset I) (y : Y) :
    y ∈ outsideVertices obj J ↔ obj y ∉ J := by
  simp only [outsideVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The vertices of matched objects that `p` carries outside the matched target. -/
def matchLeak [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y) (π : I → I)
    (Dom : Finset I) : Finset Y :=
  Finset.univ.filter fun y ↦ obj y ∈ Dom ∧ obj (p y) ≠ π (obj y)

theorem mem_matchLeak [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y) (π : I → I)
    (Dom : Finset I) (y : Y) :
    y ∈ matchLeak obj p π Dom ↔ obj y ∈ Dom ∧ obj (p y) ≠ π (obj y) := by
  simp only [matchLeak, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The vertex exceptional set of an object inequality along `p`: the vertices
outside the domain, in a bad object, or carried outside the matched target. -/
def vertexExceptional [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y) (π : I → I)
    (Dom Bad : Finset I) : Finset Y :=
  Finset.univ.filter fun y ↦ obj y ∉ Dom ∨ obj y ∈ Bad ∨ obj (p y) ≠ π (obj y)

theorem mem_vertexExceptional [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y)
    (π : I → I) (Dom Bad : Finset I) (y : Y) :
    y ∈ vertexExceptional obj p π Dom Bad ↔
      obj y ∉ Dom ∨ obj y ∈ Bad ∨ obj (p y) ≠ π (obj y) := by
  simp only [vertexExceptional, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Objects to vertices.**  An inequality between the matched objects outside
`Bad` is an inequality of the observable `f ∘ obj` along `p` off the vertex
exceptional set. -/
theorem drift_of_not_mem_vertexExceptional [DecidableEq I] (obj : Y → I)
    (p : Equiv.Perm Y) (π : I → I) (Dom Bad : Finset I) (f : I → ℝ) (κ : ℝ)
    (hobj : ∀ i ∈ Dom, i ∉ Bad → f (π i) ≤ f i + κ) (y : Y)
    (hy : y ∉ vertexExceptional obj p π Dom Bad) :
    f (obj (p y)) ≤ f (obj y) + κ := by
  rw [mem_vertexExceptional] at hy
  have hD : obj y ∈ Dom := by
    by_contra h
    exact hy (Or.inl h)
  have hB : obj y ∉ Bad := fun h ↦ hy (Or.inr (Or.inl h))
  have hπ : obj (p y) = π (obj y) := by
    by_contra h
    exact hy (Or.inr (Or.inr h))
  rw [hπ]
  exact hobj (obj y) hD hB

/-- The vertex exceptional set is at most the weight outside the domain, the
weight of the bad objects and the matching leak. -/
theorem card_vertexExceptional_le [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y)
    (π : I → I) (Dom Bad : Finset I) :
    (vertexExceptional obj p π Dom Bad).card ≤
      (outsideVertices obj Dom).card + (objectVertices obj Bad).card +
        (matchLeak obj p π Dom).card := by
  have hsub : vertexExceptional obj p π Dom Bad ⊆
      (outsideVertices obj Dom ∪ objectVertices obj Bad) ∪ matchLeak obj p π Dom := by
    intro y hy
    rw [mem_vertexExceptional] at hy
    rw [Finset.mem_union, Finset.mem_union, mem_outsideVertices, mem_objectVertices,
      mem_matchLeak]
    by_cases hD : obj y ∈ Dom
    · rcases hy with h | h | h
      · exact absurd hD h
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨hD, h⟩
    · exact Or.inl (Or.inl hD)
  calc (vertexExceptional obj p π Dom Bad).card
      ≤ ((outsideVertices obj Dom ∪ objectVertices obj Bad) ∪
          matchLeak obj p π Dom).card := Finset.card_le_card hsub
    _ ≤ (outsideVertices obj Dom ∪ objectVertices obj Bad).card +
          (matchLeak obj p π Dom).card := Finset.card_union_le _ _
    _ ≤ (outsideVertices obj Dom).card + (objectVertices obj Bad).card +
          (matchLeak obj p π Dom).card := by
        have h := Finset.card_union_le (outsideVertices obj Dom) (objectVertices obj Bad)
        omega

/-- **Vertices to objects.**  A matched object whose observable changes by more
than `δ` puts each of its vertices into the drop set of `f ∘ obj` or into the
matching leak. -/
theorem objectVertices_failing_subset [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y)
    (π : I → I) (Dom : Finset I) (f : I → ℝ) (δ : ℝ) :
    objectVertices obj (Dom.filter fun i ↦ δ < |f (π i) - f i|) ⊆
      dropSet (fun y ↦ f (obj y)) p δ ∪ matchLeak obj p π Dom := by
  intro y hy
  rw [mem_objectVertices, Finset.mem_filter] at hy
  obtain ⟨hD, hδ⟩ := hy
  rw [Finset.mem_union]
  by_cases hπ : obj (p y) = π (obj y)
  · left
    simp only [dropSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hπ]
    exact hδ
  · right
    rw [mem_matchLeak]
    exact ⟨hD, hπ⟩

theorem card_objectVertices_failing_le [DecidableEq I] (obj : Y → I) (p : Equiv.Perm Y)
    (π : I → I) (Dom : Finset I) (f : I → ℝ) (δ : ℝ) :
    (objectVertices obj (Dom.filter fun i ↦ δ < |f (π i) - f i|)).card ≤
      (dropSet (fun y ↦ f (obj y)) p δ).card + (matchLeak obj p π Dom).card :=
  (Finset.card_le_card (objectVertices_failing_subset obj p π Dom f δ)).trans
    (Finset.card_union_le _ _)

end Finite

/-! ### The logarithmic observable -/

/-- The logarithm of a natural observable, cut off below at `1`. -/
noncomputable def logObservable {I : Type*} (f : I → ℕ) (i : I) : ℝ :=
  Real.log (max (f i : ℝ) 1)

theorem logCut_monotone : Monotone fun t : ℝ ↦ Real.log (max t 1) := by
  intro a b hab
  exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right a 1))
    (max_le_max hab le_rfl)

/-- The cut logarithm of the natural median is a median of the logarithmic
observable. -/
theorem isMedian_logCut_natMedian {Y : FiniteModel} (s : Y → ℕ) :
    FiniteMultiGraph.IsMedian (fun y ↦ Real.log (max (s y : ℝ) 1))
      (Real.log (max (FiniteMultiGraph.natMedian s : ℝ) 1)) := by
  have h := isMedian_comp_monotone (FiniteMultiGraph.natMedian_isMedian s) logCut_monotone
  exact h

/-- A monotone natural observable has a monotone logarithmic observable. -/
theorem logCut_le_of_le {a b : ℕ} (h : a ≤ b) :
    Real.log (max (a : ℝ) 1) ≤ Real.log (max (b : ℝ) 1) :=
  logCut_monotone (Nat.cast_le.mpr h)

/-- **Multiplicative to additive drift.**  If `(1 - ζ) a ≤ b` with
`0 ≤ ζ ≤ 1/2`, the logarithmic observable rises from `b` to `a` by at most `2ζ`. -/
theorem logCut_le_add_of_mul_le {a b : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ₂ : ζ ≤ 1 / 2)
    (h : (1 - ζ) * (a : ℝ) ≤ b) :
    Real.log (max (a : ℝ) 1) ≤ Real.log (max (b : ℝ) 1) + 2 * ζ := by
  have hx1 : (1 : ℝ) ≤ max (a : ℝ) 1 := le_max_right _ _
  have hy1 : (1 : ℝ) ≤ max (b : ℝ) 1 := le_max_right _ _
  have hxpos : (0 : ℝ) < max (a : ℝ) 1 := lt_of_lt_of_le one_pos hx1
  have hypos : (0 : ℝ) < max (b : ℝ) 1 := lt_of_lt_of_le one_pos hy1
  have hmul : (1 - ζ) * max (a : ℝ) 1 ≤ max (b : ℝ) 1 := by
    rcases le_total (a : ℝ) 1 with ha | ha
    · rw [max_eq_right ha]
      linarith
    · rw [max_eq_left ha]
      exact h.trans (le_max_left _ _)
  have h2 : max (a : ℝ) 1 ≤ 2 * max (b : ℝ) 1 := by
    have hhalf : ζ * max (a : ℝ) 1 ≤ 1 / 2 * max (a : ℝ) 1 :=
      mul_le_mul_of_nonneg_right hζ₂ hxpos.le
    linarith
  have h3 : ζ * max (a : ℝ) 1 ≤ ζ * (2 * max (b : ℝ) 1) :=
    mul_le_mul_of_nonneg_left h2 hζ
  have hratio : max (a : ℝ) 1 / max (b : ℝ) 1 - 1 ≤ 2 * ζ := by
    rw [div_sub_one hypos.ne', div_le_iff₀ hypos]
    linarith
  have hlog : Real.log (max (a : ℝ) 1) - Real.log (max (b : ℝ) 1) ≤
      max (a : ℝ) 1 / max (b : ℝ) 1 - 1 := by
    rw [← Real.log_div hxpos.ne' hypos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
  linarith

/-- **Ratio bound.**  A logarithmic change of at most `c` between positive natural
observables bounds their ratio by `exp c`. -/
theorem le_exp_mul_of_abs_logCut_sub_le {a b : ℕ} {c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : |Real.log (max (a : ℝ) 1) - Real.log (max (b : ℝ) 1)| ≤ c) :
    (a : ℝ) ≤ Real.exp c * b := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  rw [max_eq_left ha', max_eq_left hb'] at h
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha'
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb'
  have h₁ : Real.log (a : ℝ) ≤ c + Real.log b := by
    have h' := (abs_le.mp h).2
    linarith
  have h₂ : Real.log (a : ℝ) ≤ Real.log (Real.exp c * b) := by
    rw [Real.log_mul (Real.exp_pos c).ne' hbpos.ne', Real.log_exp]
    exact h₁
  exact (Real.log_le_log_iff hapos (mul_pos (Real.exp_pos c) hbpos)).mp h₂

/-! ### Label estimates and the asymptotic vertex form -/

section Asymptotic

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

/-- A label along which the observable is invariant off a negligible set, and
which rarely crosses the ambient components, moves the clamped deviation by a
negligible total amount. -/
theorem clampedLabel_negligible_of_eqOff (D : ExpanderDecomposition S T)
    (m : ∀ n, D.componentIndex n → ℝ) (φ : ∀ n, S.model n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (g : G) (E : ∀ n, Finset (S.model n))
    (hE : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦ ((E n).card : ℝ))
    (hinv : ∀ n y, y ∉ E n → φ n (S.map n g y) = φ n y)
    (hcross : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ Nat.cast_nonneg _
  refine Negligible.mono_nonneg hN (fun n ↦ Finset.sum_nonneg fun x _ ↦ abs_nonneg _)
    (fun n ↦ ?_) (Negligible.const_mul (2 * M) (hE.add hcross))
  have hbound : ∑ x : S.model n,
      |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| ≤
      2 * M * ((E n ∪ wordCrossing (D.blocks n) (S.map n g)).card : ℝ) :=
    sum_abs_clamped_sub_le_of_eqOff (D.blocks n) (m n) (φ n) hM (S.map n g) (E n) (hinv n)
  have hcast : ((E n ∪ wordCrossing (D.blocks n) (S.map n g)).card : ℝ) ≤
      ((E n).card : ℝ) + ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (E n) (wordCrossing (D.blocks n) (S.map n g))
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcast h2M
  linarith

/-- A label with one-sided drift off a negligible set, with vanishing drift, and
which rarely crosses the ambient components, moves the clamped deviation by a
negligible total amount. -/
theorem clampedLabel_negligible_of_oneSided (D : ExpanderDecomposition S T)
    (m : ∀ n, D.componentIndex n → ℝ) (φ : ∀ n, S.model n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (κ : ℕ → ℝ) (hκ : ∀ n, 0 ≤ κ n) (hκv : Vanishing κ)
    (g : G) (E : ∀ n, Finset (S.model n))
    (hE : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦ ((E n).card : ℝ))
    (hdrift : ∀ n y, y ∉ E n → φ n (S.map n g y) ≤ φ n y + κ n)
    (hcross : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ Nat.cast_nonneg _
  have hκN : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      κ n * (Fintype.card (S.model n) : ℝ) := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (mul_nonneg (hκ n) (hN n)) (hN n))
      (fun n ↦ ?_) hκv
    show κ n * (Fintype.card (S.model n) : ℝ) / (Fintype.card (S.model n) : ℝ) ≤ κ n
    by_cases hN0 : (Fintype.card (S.model n) : ℝ) = 0
    · rw [hN0, mul_zero, zero_div]
      exact hκ n
    · rw [mul_div_assoc, div_self hN0, mul_one]
  refine Negligible.mono_nonneg hN (fun n ↦ Finset.sum_nonneg fun x _ ↦ abs_nonneg _)
    (fun n ↦ ?_)
    (Negligible.const_mul 2 (hκN.add (Negligible.const_mul (2 * M) (hE.add hcross))))
  have hbound : ∑ x : S.model n,
      |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| ≤
      2 * (κ n * (Fintype.card (S.model n) : ℝ) +
        2 * M * ((E n ∪ wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) :=
    sum_abs_clamped_sub_le_of_oneSided (D.blocks n) (m n) (φ n) hM (hκ n) (S.map n g) (E n)
      (hdrift n)
  have hcast : ((E n ∪ wordCrossing (D.blocks n) (S.map n g)).card : ℝ) ≤
      ((E n).card : ℝ) + ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (E n) (wordCrossing (D.blocks n) (S.map n g))
  have h2M : (0 : ℝ) ≤ 2 * M := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcast h2M
  linarith

/-- The clamped label variation along the approximate inverse of a label is
negligible once it is negligible along the label. -/
theorem clampedLabel_negligible_inv (D : ExpanderDecomposition S T)
    (m : ∀ n, D.componentIndex n → ℝ) (φ : ∀ n, S.model n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (g : G)
    (hg : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x|) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g⁻¹ x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ Nat.cast_nonneg _
  refine Negligible.mono_nonneg hN (fun n ↦ Finset.sum_nonneg fun x _ ↦ abs_nonneg _)
    (fun n ↦ ?_) (hg.add (Negligible.const_mul (2 * M) (S.inverseError_negligible g)))
  have hclose : ∑ x : S.model n,
      |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g⁻¹ x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| ≤
      ∑ x : S.model n,
        |clampedDeviation (D.blocks n) (m n) (φ n) M ((S.map n g)⁻¹ x) -
          clampedDeviation (D.blocks n) (m n) (φ n) M x| +
        2 * M * ((hammingDisagreement (S.map n g⁻¹) (S.map n g)⁻¹).card : ℝ) :=
    sum_abs_sub_le_of_close (fun y ↦ clampedDeviation (D.blocks n) (m n) (φ n) M y)
      (fun y ↦ abs_clampTo_le hM (φ n y - m n (blockIndexOf (D.blocks n) y)))
      ((S.map n g)⁻¹) (S.map n g⁻¹)
  have hinv : ∑ x : S.model n,
      |clampedDeviation (D.blocks n) (m n) (φ n) M ((S.map n g)⁻¹ x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x| =
      ∑ x : S.model n,
        |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n g x) -
          clampedDeviation (D.blocks n) (m n) (φ n) M x| :=
    sum_abs_sub_inv_eq (fun y ↦ clampedDeviation (D.blocks n) (m n) (φ n) M y) (S.map n g)
  have hdis : hammingDisagreement (S.map n g⁻¹) (S.map n g)⁻¹ = S.inverseError n g := rfl
  rw [hdis, hinv] at hclose
  exact hclose

/-- The componentwise median of the logarithmic observable of `f ∘ obj`. -/
noncomputable def logMedian (D : ExpanderDecomposition S T) {I : ℕ → Type}
    (obj : ∀ n, S.model n → I n) (f : ∀ n, I n → ℕ) (n : ℕ) (B : D.componentIndex n) : ℝ :=
  Real.log (max (FiniteMultiGraph.natMedian
    fun x : indexedBlockModel (D.blocks n) B ↦ f n (obj n (x : S.model n)) : ℝ) 1)

theorem isMedian_logMedian (D : ExpanderDecomposition S T) {I : ℕ → Type}
    (obj : ∀ n, S.model n → I n) (f : ∀ n, I n → ℕ) (n : ℕ) (B : D.componentIndex n) :
    FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel (D.blocks n) B ↦ logObservable (f n) (obj n (x : S.model n)))
      (logMedian D obj f n B) := by
  have h := isMedian_logCut_natMedian
    (fun x : indexedBlockModel (D.blocks n) B ↦ f n (obj n (x : S.model n)))
  exact h

/-- **Kun–Thom Lemma 4.4, vertex form.**  Let `D` be an ambient expander
decomposition, `obj` present the objects on the models and `f` a natural
observable of the objects.  If every ambient label moves the clamped logarithmic
observable by a negligible total amount, then along a permutation sequence
`S.map n g` that rarely crosses the ambient components, the matched objects whose
logarithmic observable changes by more than `2M` carry negligible weight, up to
the matching leak. -/
theorem failingWeight_negligible (D : ExpanderDecomposition S T) {I : ℕ → Type}
    [∀ n, DecidableEq (I n)] (obj : ∀ n, S.model n → I n) (f : ∀ n, I n → ℕ)
    {M : ℝ} (hM : 0 < M)
    (hlabel : ∀ t ∈ T, Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n,
        |clampedDeviation (D.blocks n) (logMedian D obj f n)
            (fun y ↦ logObservable (f n) (obj n y)) M (S.map n t x) -
          clampedDeviation (D.blocks n) (logMedian D obj f n)
            (fun y ↦ logObservable (f n) (obj n y)) M x|)
    (g : G) (π : ∀ n, I n → I n) (Dom : ∀ n, Finset (I n))
    (hcross : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ))
    (hleak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((matchLeak (obj n) (S.map n g) (π n) (Dom n)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((objectVertices (obj n) ((Dom n).filter fun i ↦
        2 * M < |logObservable (f n) (π n i) - logObservable (f n) i|)).card : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ Nat.cast_nonneg _
  have hdev := deviation_negligible D (logMedian D obj f)
    (fun n y ↦ logObservable (f n) (obj n y)) (fun n B ↦ isMedian_logMedian D obj f n B)
    hM hlabel
  have hdrop := drop_negligible D (logMedian D obj f)
    (fun n y ↦ logObservable (f n) (obj n y)) M (fun n ↦ S.map n g) hdev hcross
  refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (hdrop.add hleak)
  have hcard := card_objectVertices_failing_le (obj n) (S.map n g) (π n) (Dom n)
    (logObservable (f n)) (2 * M)
  exact_mod_cast hcard

end Asymptotic

end MedianVertexForm
end GroupApproximation
