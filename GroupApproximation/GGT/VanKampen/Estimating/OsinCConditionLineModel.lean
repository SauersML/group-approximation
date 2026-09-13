import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.Algebra.HyperbolicInteger
import GroupApproximation.Meta.AxiomGuard

/-!
# A nonempty model of Osin's condition at every `ε` and `ρ`

The W1 pieces of Osin's Lemma 9.4 in `Estimating/OsinLemma94PlanarPieces.lean`
(`OsinLemma94PolygonRealizationInput`, `OsinLemma94PolygonCountInput`,
`OsinLemma94CaseOneInput` and `OsinLemma94CaseTwoInput`) assume
`OsinCCondition D W eps mu lambda c rho` for every `eps ≥ eps0` and `rho ≥ rho0`, where the
producer chooses `eps0` and `rho0`.  A model at one `ε` or one `ρ` therefore does not show that
the assumption can hold.

* `osinCCondition_emptyFamilyModel` holds at every parameter, but its family is empty, so its
  diagrams have no relator cells, and the pieces also assume `0 < Delta.rCellCount`.
* `UnboundSmallMuCounterexample.condition` and `UnboundConjugateCounterexample.condition` are
  nonempty, but fix `ε = 0` and one `ρ`.

This file gives a nonempty model at every parameter.  The group is `ℤ`, with alphabet
`{1, -1}` and no subgroup family, and it is `0`-hyperbolic.  The family is `{a^m, a^{-m}}`,
where `a` is the generator, `ρ ≤ m` and `2ε < μ m`:

* the letters are base letters, so the depth clause is vacuous;
* `ℤ` is abelian, so the exclusion clause of a piece, `listVal v' ≠ y (listVal v) y⁻¹`, makes
  the two words different, and a prefix of `a^m` matched against a prefix of `a^{-m}` up to
  two words of length at most `ε` has at most `2ε` letters;
* the words are geodesic, so they are `(λ, c)`-quasi-geodesic for `λ ≤ 1` and `0 ≤ c`.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.OsinCConditionLineModel

open GroupApproximation.HullSC GroupApproximation.WordMetric

/-- The infinite cyclic group, written multiplicatively. -/
abbrev G := Multiplicative ℤ

/-- The relative generating set `({1, -1}, ∅)` of `ℤ`. -/
def D : RelGenSet G Empty where
  base := Hyperbolic.intAlphabet
  fam := Empty.elim
  symmetricGenerating := by
    convert Hyperbolic.isSymmetricGeneratingSet_intAlphabet using 1
    ext x
    simp

theorem alphabet_carrier : D.alphabet.carrier = Hyperbolic.intAlphabet := by
  show Hyperbolic.intAlphabet ∪ ⋃ lam : Empty, ((D.fam lam : Subgroup G) : Set G) =
    Hyperbolic.intAlphabet
  ext x
  simp

/-- The line is `0`-hyperbolic. -/
theorem hyperbolic : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier 0 := by
  rw [alphabet_carrier]
  exact Hyperbolic.isFourPointHyperbolic_intAlphabet

/-- The generator `1` as a base letter. -/
def a : RelLetter G Empty := .base (Multiplicative.ofAdd 1)

/-- The generator `-1` as a base letter. -/
def b : RelLetter G Empty := .base (Multiplicative.ofAdd (-1))

/-- The family `{a^m, a^{-m}}`. -/
def W (m : ℕ) : Set (List (RelLetter G Empty)) :=
  {List.replicate m a, List.replicate m b}

theorem mem_W {m : ℕ} {w : List (RelLetter G Empty)} (hw : w ∈ W m) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      w = List.replicate m (RelLetter.base (Multiplicative.ofAdd s) : RelLetter G Empty) := by
  rcases hw with hw | hw
  · exact ⟨1, Or.inl rfl, hw⟩
  · exact ⟨-1, Or.inr rfl, Set.mem_singleton_iff.mp hw⟩

theorem length_of_mem {m : ℕ} {w : List (RelLetter G Empty)} (hw : w ∈ W m) :
    w.length = m := by
  obtain ⟨s, _, rfl⟩ := mem_W hw
  simp only [List.length_replicate]

theorem toAdd_ofAdd_pow (s : ℤ) (n : ℕ) :
    Multiplicative.toAdd (Multiplicative.ofAdd s ^ n) = (n : ℤ) * s := by
  rw [toAdd_pow, toAdd_ofAdd, Int.nsmul_eq_mul]

theorem listVal_replicate (m : ℕ) (g : G) :
    RelLetter.listVal (List.replicate m (RelLetter.base g : RelLetter G Empty)) = g ^ m := by
  simp [RelLetter.listVal, RelLetter.val]

theorem revInv_replicate (g : G) (m : ℕ) :
    RelWord.revInv (List.replicate m (RelLetter.base g : RelLetter G Empty)) =
      List.replicate m (RelLetter.base g⁻¹) := by
  simp [RelWord.revInv, RelWord.inv]

theorem prefix_value {m : ℕ} {g : G} {first suffix : List (RelLetter G Empty)}
    (hsplit : List.replicate m (RelLetter.base g : RelLetter G Empty) = first ++ suffix) :
    RelLetter.listVal first = g ^ first.length ∧ first.length ≤ m := by
  have hlen := (List.replicate_eq_append_iff.mp hsplit).1
  have hfirst := (List.replicate_eq_append_iff.mp hsplit).2.1
  refine ⟨?_, by omega⟩
  conv_lhs => rw [hfirst]
  simp [RelLetter.listVal, RelLetter.val]

/-- A word of length at most `ε` in `{1, -1}` names an integer of absolute value at most `ε`. -/
theorem natAbs_le_of_wordNorm_le {y : G} {eps : ℕ}
    (hy : wordNorm D.alphabet.carrier y ≤ eps) : (Multiplicative.toAdd y).natAbs ≤ eps := by
  rw [alphabet_carrier] at hy
  have h := Hyperbolic.wordNorm_ofAdd (Multiplicative.toAdd y)
  rw [ofAdd_toAdd] at h
  omega

theorem conj_line (y x : G) : y * x * y⁻¹ = x := by
  rw [mul_comm y x, mul_inv_cancel_right]

/-- **Pieces are short.**  Both prefixes of a piece of the family have at most `2ε` letters:
the exclusion clause makes the two words different, and then the prefixes point in opposite
directions. -/
theorem piece_lengths_le {m eps : ℕ} {first second v v' : List (RelLetter G Empty)}
    (hv : v ∈ W m) (hs : ∃ s, v = first ++ s) (hv' : v' ∈ W m)
    (hs' : ∃ s', v' = second ++ s') {y z : G}
    (hy : wordNorm D.alphabet.carrier y ≤ eps) (hz : wordNorm D.alphabet.carrier z ≤ eps)
    (heq : RelLetter.listVal second = y * RelLetter.listVal first * z)
    (hne : RelLetter.listVal v' ≠ y * RelLetter.listVal v * y⁻¹) :
    first.length ≤ 2 * eps ∧ second.length ≤ 2 * eps := by
  obtain ⟨s₁, hs₁, rfl⟩ := mem_W hv
  obtain ⟨s₂, hs₂, rfl⟩ := mem_W hv'
  obtain ⟨suffix, hsplit⟩ := hs
  obtain ⟨suffix', hsplit'⟩ := hs'
  obtain ⟨hval, _⟩ := prefix_value hsplit
  obtain ⟨hval', _⟩ := prefix_value hsplit'
  have hy' := natAbs_le_of_wordNorm_le hy
  have hz' := natAbs_le_of_wordNorm_le hz
  rw [conj_line, listVal_replicate, listVal_replicate] at hne
  have hne' : (m : ℤ) * s₂ ≠ (m : ℤ) * s₁ := by
    intro h
    apply hne
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd_pow, toAdd_ofAdd_pow]
    exact h
  have he := congrArg Multiplicative.toAdd heq
  rw [hval, hval', toAdd_mul, toAdd_mul, toAdd_ofAdd_pow, toAdd_ofAdd_pow] at he
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> omega

theorem admissible_replicate {m : ℕ} {s : ℤ} (hs : s = 1 ∨ s = -1) :
    RelWord.IsAdmissible D
      (List.replicate m (RelLetter.base (Multiplicative.ofAdd s) : RelLetter G Empty)) := by
  intro letter hletter
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hletter
  show Multiplicative.ofAdd s ∈ Hyperbolic.intAlphabet
  exact Hyperbolic.mem_intAlphabet_iff.mpr (by simpa using hs)

theorem vertex_replicate (g v : G) (m i : ℕ) (hi : i ≤ m) :
    OsinComponents.vertex v (List.replicate m (RelLetter.base g : RelLetter G Empty)) i =
      v * g ^ i := by
  induction m generalizing v i with
  | zero =>
      obtain rfl : i = 0 := by omega
      simp
  | succ m ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hstep : (RelLetter.base g : RelLetter G Empty).val = g := rfl
          rw [List.replicate_succ, OsinComponents.vertex_cons_succ, hstep,
            ih (v * g) i (by omega), pow_succ', mul_assoc]

/-- The words `a^{±m}` are geodesic, so they are `(λ, c)`-quasi-geodesic. -/
theorem quasiGeodesic_replicate {m : ℕ} {s : ℤ} (hs : s = 1 ∨ s = -1) {lambda c : ℝ}
    (hlambda : lambda ≤ 1) (hc : 0 ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c
      (List.replicate m (RelLetter.base (Multiplicative.ofAdd s) : RelLetter G Empty)) := by
  refine ⟨admissible_replicate hs, ?_⟩
  intro i j hij hj
  rw [List.length_replicate] at hj
  rw [vertex_replicate (Multiplicative.ofAdd s) 1 m i (by omega),
    vertex_replicate (Multiplicative.ofAdd s) 1 m j hj, one_mul, one_mul, alphabet_carrier,
    Hyperbolic.wordDist_intAlphabet, toAdd_ofAdd_pow, toAdd_ofAdd_pow]
  have hd : (-((i : ℤ) * s) + (j : ℤ) * s).natAbs = j - i := by
    rcases hs with rfl | rfl <;> omega
  rw [hd]
  have hx : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Osin's condition for `{a^m, a^{-m}}`**, for `0 ≤ c`, `λ ≤ 1`, `ρ ≤ m` and `2ε < μ m`. -/
theorem condition (eps rho m : ℕ) {mu lambda c : ℝ} (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hrho : rho ≤ m) (hm : 2 * (eps : ℝ) < mu * m) :
    OsinCCondition D (W m) eps mu lambda c rho := by
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
    obtain ⟨s, hs, rfl⟩ := mem_W hw
    exact admissible_replicate hs
  · intro w hw
    obtain ⟨s, hs, rfl⟩ := mem_W hw
    rw [revInv_replicate, ← ofAdd_neg]
    rcases hs with rfl | rfl
    · right
      exact rfl
    · rw [neg_neg]
      left
      exact rfl
  · intro w hw n
    obtain ⟨s, _, rfl⟩ := mem_W hw
    rwa [List.rotate_replicate]
  · intro w hw
    rw [length_of_mem hw]
    exact hrho
  · intro w _ letter _ lam
    exact Empty.elim lam
  · intro first v hp
    obtain ⟨hv, hs, other, ho, _, second, suffix, hsplit, y, z, hy, hz, heq, hne⟩ := hp
    have hfirst := (piece_lengths_le hv hs ho ⟨suffix, hsplit⟩ hy hz heq hne).1
    rw [length_of_mem hv]
    have h1 : (first.length : ℝ) ≤ 2 * (eps : ℝ) := by exact_mod_cast hfirst
    linarith
  · intro w hw
    obtain ⟨s, hs, rfl⟩ := mem_W hw
    exact quasiGeodesic_replicate hs hlambda hc
  · intro first second v hp
    obtain ⟨hv, hs, other, ho, suffix, hsplit, y, z, hy, hz, heq, hne⟩ := hp
    obtain ⟨hfirst, hsecond⟩ := piece_lengths_le hv hs ho ⟨suffix, hsplit⟩ hy hz heq hne
    rw [length_of_mem hv]
    have h1 : (first.length : ℝ) ≤ 2 * (eps : ℝ) := by exact_mod_cast hfirst
    have h2 : (second.length : ℝ) ≤ 2 * (eps : ℝ) := by exact_mod_cast hsecond
    exact max_lt (by linarith) (by linarith)

/-- **The C-condition layer of the W1 piece assumptions can hold.**  For all `0 < λ ≤ 1`,
`0 ≤ c`, `0 < μ` and every `ε` and `ρ`, the `0`-hyperbolic line carries a family satisfying
`OsinCCondition` that contains a word of positive length at least `ρ`. -/
def OsinCConditionLineModelStatement : Prop :=
  ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu →
    ∀ eps rho : ℕ, ∃ W : Set (List (RelLetter G Empty)),
      (∃ w ∈ W, rho ≤ w.length ∧ 0 < w.length) ∧ OsinCCondition D W eps mu lambda c rho

theorem osinCConditionLineModel : OsinCConditionLineModelStatement := by
  intro lambda c mu _ hlambda hc hmu eps rho
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (eps : ℝ) / mu)
  have hk' : 2 * (eps : ℝ) < mu * k := by
    have h := (div_lt_iff₀ hmu).mp hk
    linarith [mul_comm (k : ℝ) mu]
  refine ⟨W (rho + k + 1), ⟨List.replicate (rho + k + 1) a, Or.inl rfl, ?_, ?_⟩, ?_⟩
  · simp only [List.length_replicate]
    omega
  · simp only [List.length_replicate]
    omega
  · refine condition eps rho (rho + k + 1) hlambda hc (by omega) ?_
    have hmk : mu * (k : ℝ) ≤ mu * ((rho + k + 1 : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hmu.le
      exact_mod_cast (show k ≤ rho + k + 1 by omega)
    linarith

end GroupApproximation.GGT.VanKampen.Estimating.OsinCConditionLineModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.OsinCConditionLineModel.osinCConditionLineModel
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.OsinCConditionLineModel.hyperbolic
