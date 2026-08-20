import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# The infinite cyclic group is `0`-hyperbolic

`Algebra/HyperbolicGroup.lean` proves that finite groups are hyperbolic, which
alone would leave `IsHyperbolicGroup` open to the objection that it is a
statement about bounded metrics.  This module computes the word metric of
`Multiplicative ℤ` with respect to the alphabet `{1, -1}` exactly --- it is
`|m - n|` --- and checks Gromov's four-point condition on it at `δ = 0`.

That the real line is `0`-hyperbolic is the standard first example: among the
three pairings `d(w,x) + d(y,z)`, `d(w,y) + d(x,z)`, `d(w,z) + d(x,y)` of four
points of `ℝ`, the two largest are equal, so each is bounded by the maximum of
the other two.  Here the four points are integers and the whole verification is
linear arithmetic over `ℤ`, once the metric has been identified.

Together with `isPowerTorsionFree_multiplicative_int` and
`infinite_multiplicative_int` this exhibits an **infinite torsion-free
hyperbolic group**.  It does not have property `(T)` ---
`Kazhdan/IntegerNotKazhdan.lean` proves that it does not --- and that is the
point: the two easy clauses of the target statement are satisfiable by an
infinite group with no difficulty at all, and property `(T)` is the clause that
carries the whole weight.  `Kazhdan/TorsionFreeHyperbolicKazhdan.lean` records
that contrast.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

/-- The standard alphabet `{1, -1}` of the infinite cyclic group. -/
def intAlphabet : Set (Multiplicative ℤ) :=
  {Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (-1 : ℤ)}

/-- Membership in the alphabet, read off through `toAdd`. -/
theorem mem_intAlphabet_iff {a : Multiplicative ℤ} :
    a ∈ intAlphabet ↔ Multiplicative.toAdd a = 1 ∨ Multiplicative.toAdd a = -1 := by
  constructor
  · intro ha
    simp only [intAlphabet, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro ha
    simp only [intAlphabet, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha with h | h
    · exact Or.inl (Multiplicative.toAdd.injective h)
    · exact Or.inr (Multiplicative.toAdd.injective h)

/-- `{1, -1}` is a symmetric generating set of the infinite cyclic group. -/
theorem isSymmetricGeneratingSet_intAlphabet :
    IsSymmetricGeneratingSet intAlphabet := by
  constructor
  · intro x hx
    rcases mem_intAlphabet_iff.mp hx with h | h
    · have hx1 : x = Multiplicative.ofAdd (1 : ℤ) := Multiplicative.ext h
      subst hx1
      exact mem_intAlphabet_iff.mpr (Or.inr (by simp))
    · have hx1 : x = Multiplicative.ofAdd (-1 : ℤ) := Multiplicative.ext h
      subst hx1
      exact mem_intAlphabet_iff.mpr (Or.inl (by simp))
  · rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = x :=
      ⟨Multiplicative.toAdd x, rfl⟩
    induction n using Int.induction_on with
    | zero =>
        -- `ofAdd 0` is definitionally `1`
        exact one_mem _
    | succ i ih =>
        rw [ofAdd_add]
        exact mul_mem ih (Subgroup.subset_closure (mem_intAlphabet_iff.mpr (Or.inl rfl)))
    | pred i ih =>
        have hsub : (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) := by ring
        rw [hsub, ofAdd_add]
        exact mul_mem ih (Subgroup.subset_closure (mem_intAlphabet_iff.mpr (Or.inr rfl)))

/-! ## The word length is the absolute value -/

/-- **Upper bound.**  The element `n` is spelled by `|n|` letters. -/
theorem wordNorm_ofAdd_le (n : ℤ) :
    wordNorm intAlphabet (Multiplicative.ofAdd n) ≤ n.natAbs := by
  induction n using Int.induction_on with
  | zero =>
      -- `ofAdd 0` is definitionally `1`, so this is `wordNorm_one`
      have h0 : wordNorm intAlphabet (Multiplicative.ofAdd (0 : ℤ)) = 0 :=
        wordNorm_one intAlphabet
      omega
  | succ i ih =>
      rw [ofAdd_add]
      have hmul := wordNorm_mul_le isSymmetricGeneratingSet_intAlphabet
        (Multiplicative.ofAdd (i : ℤ)) (Multiplicative.ofAdd (1 : ℤ))
      have hone : wordNorm intAlphabet (Multiplicative.ofAdd (1 : ℤ)) ≤ 1 :=
        wordNorm_le_one_of_mem (mem_intAlphabet_iff.mpr (Or.inl rfl))
      omega
  | pred i ih =>
      have hsub : (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) := by ring
      rw [hsub, ofAdd_add]
      have hmul := wordNorm_mul_le isSymmetricGeneratingSet_intAlphabet
        (Multiplicative.ofAdd (-(i : ℤ))) (Multiplicative.ofAdd (-1 : ℤ))
      have hone : wordNorm intAlphabet (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 :=
        wordNorm_le_one_of_mem (mem_intAlphabet_iff.mpr (Or.inr rfl))
      omega

/-- A word in `{1, -1}` of length `k` spells an integer lying in `[-k, k]`:
each letter moves the partial sum by exactly one. -/
theorem toAdd_prod_bounds : ∀ l : List (Multiplicative ℤ), (∀ a ∈ l, a ∈ intAlphabet) →
    -(l.length : ℤ) ≤ Multiplicative.toAdd l.prod ∧
      Multiplicative.toAdd l.prod ≤ (l.length : ℤ) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro hmem
      have ha : Multiplicative.toAdd a = 1 ∨ Multiplicative.toAdd a = -1 :=
        mem_intAlphabet_iff.mp (hmem a (by simp))
      have ht : ∀ b ∈ t, b ∈ intAlphabet := fun b hb => hmem b (by simp [hb])
      obtain ⟨h1, h2⟩ := ih ht
      have hprod : Multiplicative.toAdd (a :: t).prod
          = Multiplicative.toAdd a + Multiplicative.toAdd t.prod := by
        simp
      have hlen : (((a :: t).length : ℤ)) = (t.length : ℤ) + 1 := by
        simp
      rw [hprod, hlen]
      omega

/-- **Lower bound.**  No word shorter than `|n|` spells `n`. -/
theorem natAbs_le_length_of_isWord {l : List (Multiplicative ℤ)} {n : ℤ}
    (h : IsWord intAlphabet l (Multiplicative.ofAdd n)) : n.natAbs ≤ l.length := by
  obtain ⟨h1, h2⟩ := toAdd_prod_bounds l h.letters
  rw [h.prod_eq] at h1 h2
  have hn : Multiplicative.toAdd (Multiplicative.ofAdd n) = n := rfl
  rw [hn] at h1 h2
  omega

/-- **The word length of the infinite cyclic group is the absolute value.** -/
theorem wordNorm_ofAdd (n : ℤ) :
    wordNorm intAlphabet (Multiplicative.ofAdd n) = n.natAbs := by
  refine le_antisymm (wordNorm_ofAdd_le n) ?_
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq isSymmetricGeneratingSet_intAlphabet (Multiplicative.ofAdd n)
  have hbound := natAbs_le_length_of_isWord hl
  omega

/-- **The word metric of the infinite cyclic group is the distance on the
line.** -/
theorem wordDist_intAlphabet (x y : Multiplicative ℤ) :
    wordDist intAlphabet x y
      = (-Multiplicative.toAdd x + Multiplicative.toAdd y).natAbs := by
  have hxy : x⁻¹ * y
      = Multiplicative.ofAdd (-Multiplicative.toAdd x + Multiplicative.toAdd y) := by
    apply Multiplicative.ext
    simp
  show wordNorm intAlphabet (x⁻¹ * y) = _
  rw [hxy, wordNorm_ofAdd]

/-! ## Hyperbolicity -/

/-- **The line is `0`-hyperbolic.**  With the metric identified, the four-point
condition is an inequality between absolute values of integers. -/
theorem isFourPointHyperbolic_intAlphabet : IsFourPointHyperbolic intAlphabet 0 := by
  intro w x y z
  simp only [wordDist_intAlphabet]
  omega

/-- The alphabet `{1, -1}`, as a `Finset`. -/
def intAlphabetFinset : Finset (Multiplicative ℤ) :=
  {Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (-1 : ℤ)}

@[simp] theorem coe_intAlphabetFinset :
    (intAlphabetFinset : Set (Multiplicative ℤ)) = intAlphabet := by
  simp [intAlphabetFinset, intAlphabet]

/-- **The infinite cyclic group is hyperbolic**, at `δ = 0`. -/
theorem isHyperbolicGroup_multiplicative_int : IsHyperbolicGroup (Multiplicative ℤ) := by
  refine ⟨intAlphabetFinset, ?_, 0, ?_⟩
  · rw [coe_intAlphabetFinset]
    exact isSymmetricGeneratingSet_intAlphabet
  · rw [coe_intAlphabetFinset]
    exact isFourPointHyperbolic_intAlphabet

/-! ## The other two clauses -/

/-- The infinite cyclic group is torsion-free. -/
theorem isPowerTorsionFree_multiplicative_int : IsPowerTorsionFree (Multiplicative ℤ) := by
  intro g n hn hpow
  have h1 : Multiplicative.toAdd (g ^ n) = Multiplicative.toAdd (1 : Multiplicative ℤ) := by
    rw [hpow]
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at h1
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hg : Multiplicative.toAdd g = 0 := (mul_eq_zero.mp h1).resolve_left hn'
  exact Multiplicative.ext hg

/-- The infinite cyclic group is infinite. -/
theorem infinite_multiplicative_int : Infinite (Multiplicative ℤ) :=
  Infinite.of_injective (⇑Multiplicative.ofAdd) Multiplicative.ofAdd.injective

/-- **An infinite torsion-free hyperbolic group exists.**  Property `(T)` is the
clause this witness fails; see `Kazhdan/IntegerNotKazhdan.lean`. -/
theorem exists_infinite_torsionFree_hyperbolic :
    ∃ (G : Type) (_ : Group G),
      Infinite G ∧ IsPowerTorsionFree G ∧ IsHyperbolicGroup G :=
  ⟨Multiplicative ℤ, inferInstance, infinite_multiplicative_int,
    isPowerTorsionFree_multiplicative_int, isHyperbolicGroup_multiplicative_int⟩

end Hyperbolic
end GroupApproximation
