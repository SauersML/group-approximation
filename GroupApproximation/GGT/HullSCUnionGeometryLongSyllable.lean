import GroupApproximation.GGT.HullSCUnionGeometryElliptic

/-!
# The long-syllable branch: back into a single factor

For `k = a⁻¹ · (of x) · a` conjugate into the factor `G i`, the conjugator `a` is
*not* bounded --- one of its syllables may be arbitrarily long.  But that
syllable lies in `G i` itself, so it is absorbed into `x`:
`exists_normalise_conj` writes `a = of y · a'` with `y ∈ G i` and `a'` avoiding
the factor `i`, and then `k = a'⁻¹ · of (y⁻¹xy) · a'` with *no* cancellation at
either seam.  So `2|a'| ≤ |k|` --- the corrected conjugator is bounded --- and the
whole of the unbounded part has been moved inside the factor.

Doing that on both sides is the branch:

* on `k` with conjugator `a`, giving `y`, `a'` and the letter `x' = y⁻¹xy`;
* on `t⁻¹kt = (at)⁻¹ · (of x) · (at)` with conjugator `a·t`, giving `w`, `b'` and
  the letter `w⁻¹xw`.

The two letters are conjugate *inside the factor* by `σ = y⁻¹w`, and
`t = a'⁻¹ · (of σ) · b'`.  `exists_factor_displacement` records the three
consequences:

    |x'|ᵢ ≤ |k| ,   |σ⁻¹x'σ|ᵢ ≤ |t⁻¹kt| ,   2|t| ≤ |k| + |t⁻¹kt| + 2|σ|ᵢ .

The first two say `x'` lies in the factor's own conjugation displacement set at
`σ`; the third says `|σ|ᵢ` is large as soon as `|t|` is.  So the factor's
acylindricity --- in the conjugation form of
`isAcylindrical_cayley_of_conjDisplacement`, applied at the factor's Hull
generating set --- bounds how many `x'` there are, which is the count this branch
was for.

Note what is *not* needed: no projection to a vertex space, and no choice of
"the" long syllable of `t`.  The syllable that matters is produced by the
normalisation itself, as `σ = y⁻¹w`, and the third inequality is what makes it
long.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section LongSyllable

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- A conjugate of a nontrivial element is nontrivial. -/
theorem conj_ne_one {i : ι} {x y : G i} (hx : x ≠ 1) :
    (y⁻¹ * x * y : G i) ≠ 1 := by
  intro hcon
  refine hx ?_
  have hx' : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [hx', hcon]
  group

/-- **A letter of the union alphabet costs its factor length.** -/
theorem wordNorm_of_single_eq (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι}
    (x : G i) :
    wordNorm (unionCarrier S) (CoprodI.of x) = wordNorm (S i) x := by
  by_cases hx : x = 1
  · rw [hx, map_one, wordNorm_one, wordNorm_one]
  · rw [wordNorm_eq_syllableNorm hS]
    show wsum S (Word.equiv (CoprodI.of x : CoprodI G)) = wordNorm (S i) x
    simp [wsum, toList_equiv_of_single hx]

/-- **Normalising a conjugator against the factor it conjugates into.**  At most
one syllable of `a` lies in the factor `i`, and it is absorbed into `x`; what is
left avoids `i`. -/
theorem exists_normalise_conj {i : ι} {x : G i} (hx : x ≠ 1) (a : CoprodI G) :
    ∃ (y : G i) (a' : CoprodI G), a = CoprodI.of y * a' ∧
      Word.fstIdx (Word.equiv a') ≠ some i ∧ (y⁻¹ * x * y : G i) ≠ 1 := by
  by_cases ha : Word.fstIdx (Word.equiv a) = some i
  · obtain ⟨u, hu⟩ := exists_lead_index ha
    obtain ⟨a', haeq, -, ha'idx, -⟩ := exists_split_toList hu
    exact ⟨u, a', haeq, ha'idx, conj_ne_one hx⟩
  · refine ⟨1, a, ?_, ha, ?_⟩
    · rw [map_one, one_mul]
    · simpa using hx

/-- **The normal form of a factor conjugate.**  After normalisation nothing
cancels, so the corrected conjugator is bounded by the element itself. -/
theorem exists_conj_normal_form (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {i : ι} {x : G i} (hx : x ≠ 1) (a : CoprodI G) :
    ∃ (y : G i) (a' : CoprodI G), a = CoprodI.of y * a' ∧
      Word.fstIdx (Word.equiv a') ≠ some i ∧
      (y⁻¹ * x * y : G i) ≠ 1 ∧
      wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a)
        = 2 * wordNorm (unionCarrier S) a' + wordNorm (S i) (y⁻¹ * x * y) := by
  obtain ⟨y, a', haeq, ha'idx, hxy⟩ := exists_normalise_conj hx a
  refine ⟨y, a', haeq, ha'idx, hxy, ?_⟩
  have heq : a⁻¹ * CoprodI.of x * a
      = a'⁻¹ * CoprodI.of (y⁻¹ * x * y) * a' := by
    rw [haeq, map_mul, map_mul, map_inv]
    group
  rw [heq, wordNorm_conj_single_of_fstIdx_ne hS hxy ha'idx,
    wordNorm_of_single_eq hS]

/-- **The long-syllable branch.**  A conjugate of a factor element, together with
its conjugate by `t`, produces a letter `x'` of the factor and a factor element
`σ` with `x'` in the factor's conjugation displacement set at `σ`, and `|σ|ᵢ`
bounded below by `|t|`.

So once `|t|` is large the count is the *factor's* acylindricity at `σ`, in the
conjugation form of `isAcylindrical_cayley_of_conjDisplacement`. -/
theorem exists_factor_displacement (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {i : ι} {x : G i} (hx : x ≠ 1) (a t : CoprodI G) :
    ∃ x' σ : G i, x' ≠ 1 ∧
      wordNorm (S i) x'
          ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a) ∧
      wordNorm (S i) (σ⁻¹ * x' * σ)
          ≤ wordNorm (unionCarrier S) (t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t) ∧
      2 * wordNorm (unionCarrier S) t
          ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a)
            + wordNorm (unionCarrier S) (t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t)
            + 2 * wordNorm (S i) σ := by
  obtain ⟨y, a', haeq, -, hxy, hknorm⟩ := exists_conj_normal_form hS hx a
  obtain ⟨w, b', hbeq, -, -, htnorm⟩ := exists_conj_normal_form hS hx (a * t)
  have hconj : t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t
      = (a * t)⁻¹ * CoprodI.of x * (a * t) := by group
  have hteq : t = a'⁻¹ * CoprodI.of (y⁻¹ * w) * b' := by
    have h1 : t = a⁻¹ * (a * t) := by group
    rw [h1, hbeq, haeq, map_mul, map_inv]
    group
  have hnorm_t : wordNorm (unionCarrier S) t
      ≤ wordNorm (unionCarrier S) a' + wordNorm (S i) (y⁻¹ * w)
        + wordNorm (unionCarrier S) b' := by
    have hC := isSymmetricGeneratingSet_unionCarrier hS
    have hsub1 := wordNorm_mul_le hC (a'⁻¹ * CoprodI.of (y⁻¹ * w)) b'
    have hsub2 := wordNorm_mul_le hC a'⁻¹ (CoprodI.of (y⁻¹ * w))
    have hinv := wordNorm_inv hC a'
    have hof := wordNorm_of_single_eq hS (y⁻¹ * w)
    rw [hteq]
    omega
  refine ⟨y⁻¹ * x * y, y⁻¹ * w, hxy, ?_, ?_, ?_⟩
  · omega
  · have hx'' : ((y⁻¹ * w)⁻¹ * (y⁻¹ * x * y) * (y⁻¹ * w) : G i) = w⁻¹ * x * w := by
      group
    rw [hx'', hconj]
    omega
  · rw [hconj]
    omega

end LongSyllable

end HullSCUnionGeometry
end GroupApproximation
