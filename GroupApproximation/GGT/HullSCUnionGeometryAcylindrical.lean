import GroupApproximation.GGT.HullSCUnionGeometryCoprod

/-!
# Towards acylindricity of the union alphabet

The second clause of `HullSC.FreeProductUnionGeometryStatement` --- that the
translation action of `E ∗ H` on `Γ(E ∗ H, A ⊔ B)` is acylindrical --- is not
proved here.  This module supplies the two things any proof of it needs and the
repository does not have, and removes the one quantifier that can be removed.

## 1.  Reading the *back* of a reduced word

`GGT/HullSCUnionGeometryNormalForm.lean` is front-oriented, because Mathlib's
`Monoid.CoprodI.Word` API is: `Word.fstIdx` reads the first letter and the
`MulAction` multiplies on the left.  Every estimate about a conjugate
`t⁻¹ k t`, however, has a seam at the *back* as well.

Inversion supplies it at no cost: the last syllable of `u` is the inverse of the
first syllable of `u⁻¹`, and the union word length is inversion-invariant.  So
`wordNorm_mul_of_seam`, `wordNorm_mul_of_seam_same` and
`wordNorm_mul_of_seam_cancel` are the three branch lemmas read at the back of
the left factor instead of the front of both, and they are what turn a statement
about `u * y` into a statement about `u⁻¹` and `y`.

## 2.  The syllable count is bounded by the word length

`sylLength_le_wordNorm`: every syllable of a reduced word is nontrivial, so it
costs at least one letter.  This is the comparison between the union metric and
the *syllable* metric --- the word metric of the alphabet whose letters are the
whole factors --- and every tree argument about a free product is a statement in
the second metric transported along it.

## 3.  Acylindricity is a statement about conjugation

`isAcylindrical_cayley_of_conjDisplacement`: on a Cayley graph the two-point
displacement set at `(x,y)` is the conjugate by `x` of
`conjDisplacement A ε (x⁻¹y)`, so acylindricity needs to be checked only against
the identity and one further point.  This is the shape in which the free-product
estimate is naturally stated: for `t` long, bound

    {k : |k| ≤ ε and |t⁻¹ k t| ≤ ε}.

## What is genuinely missing, and one route that does not work

A tempting reduction is: pass to the syllable metric, observe that `E ∗ H` acts
on the Bass-Serre tree with trivial edge stabilisers, and conclude that a `k ≠ 1`
displacing two points of the tree by at most `ε` forces those points within `2ε`
of each other --- which would bound the syllable length of `t` and leave only
the "one long syllable" case, where the factor's own acylindricity finishes.

That reduction is false.  The tree-level inequality it needs,

    n(k) + n(t⁻¹ k t) ≥ 2 n(t)   for k ≠ 1,

fails for `k` loxodromic on the tree and `t` a power of `k`: in `E ∗ H` with
`k = e * h` cyclically reduced and `t = k ^ 10` one has `n(k) = 2`,
`t⁻¹ k t = k`, and `n(t) = 20`.  The lineal case is real, and any proof has to
treat it: the elements of the displacement set that are loxodromic on the tree
share an axis, and it is the triviality of the *pointwise* stabiliser of a
segment, not of an edge, that bounds how many of them there are.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

section Seam

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  The branch lemmas, read at the back -/

/-- **Nothing cancels at a seam between different factors.**  The last syllable
of `u` is the first syllable of `u⁻¹`, so this is `wordNorm_branch` at `u⁻¹`. -/
theorem wordNorm_mul_of_seam (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {u y : CoprodI G}
    (h : Word.fstIdx (Word.equiv u⁻¹) ≠ Word.fstIdx (Word.equiv y)) :
    wordNorm (unionCarrier S) (u * y)
      = wordNorm (unionCarrier S) u + wordNorm (unionCarrier S) y := by
  have hb : wordNorm (unionCarrier S) ((u⁻¹)⁻¹ * y)
      = wordNorm (unionCarrier S) u⁻¹ + wordNorm (unionCarrier S) y :=
    wordNorm_branch hS h
  rw [inv_inv] at hb
  rwa [wordNorm_inv (isSymmetricGeneratingSet_unionCarrier hS)] at hb

/-- **Exactly the two syllables at the seam merge**, when the last syllable of
`u` and the first of `y` lie in one factor and do not cancel. -/
theorem wordNorm_mul_of_seam_same (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {i : ι} {u v : G i} {x y : CoprodI G} (hx : lead x⁻¹ = some ⟨i, u⟩)
    (hy : lead y = some ⟨i, v⟩) (huv : u ≠ v) :
    wordNorm (unionCarrier S) (x * y) + wordNorm (S i) u + wordNorm (S i) v
      = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y
        + wordNorm (S i) (u⁻¹ * v) := by
  have hb := wordNorm_branch_same hS hx hy huv
  rw [inv_inv] at hb
  rwa [wordNorm_inv (isSymmetricGeneratingSet_unionCarrier hS)] at hb

/-- **At least the two syllables at the seam cancel**, when they agree. -/
theorem wordNorm_mul_of_seam_cancel (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {i : ι} {u : G i} {x y : CoprodI G} (hx : lead x⁻¹ = some ⟨i, u⟩)
    (hy : lead y = some ⟨i, u⟩) :
    wordNorm (unionCarrier S) (x * y) + 2 * wordNorm (S i) u
      ≤ wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y := by
  have hb := wordNorm_same_lead hS hx hy
  rw [inv_inv] at hb
  rwa [wordNorm_inv (isSymmetricGeneratingSet_unionCarrier hS)] at hb

/-! ## 2.  The syllable count is bounded by the union word length -/

/-- **The syllable count is at most the union word length.**  Every letter of a
reduced word is nontrivial in its own factor, so it costs at least one letter of
the union alphabet.

This is the comparison of the union metric with the syllable metric --- the word
metric of the alphabet whose letters are the whole factors --- in which every
tree argument about a free product lives. -/
theorem sylLength_le_wordNorm (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    (g : CoprodI G) : sylLength g ≤ wordNorm (unionCarrier S) g := by
  have key : ∀ l : List (Σ i, G i), (∀ p ∈ l, p.2 ≠ 1) →
      l.length ≤ (l.map fun q => wordNorm (S q.1) q.2).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
        intro hne
        have h1 : 1 ≤ wordNorm (S p.1) p.2 :=
          one_le_wordNorm (hS p.1) (hne p (by simp))
        have h2 := ih fun q hq => hne q (List.mem_cons_of_mem p hq)
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  rw [wordNorm_eq_syllableNorm hS]
  exact key (Word.equiv g).toList (Word.equiv g).ne_one

end Seam

/-! ## 3.  Acylindricity is a statement about conjugation -/

section Conj

universe u

variable {G : Type u} [Group G]

/-- **The conjugation displacement set**: the elements that both stay within `ε`
of the identity and stay within `ε` of it after conjugation by `t`.  On a Cayley
graph this is what a two-point displacement set becomes once the first point is
translated to the basepoint. -/
def conjDisplacement (A : Alphabet G) (ε : ℝ) (t : G) : Set G :=
  {k : G | ((wordNorm A.carrier k : ℕ) : ℝ) ≤ ε ∧
    ((wordNorm A.carrier (t⁻¹ * k * t) : ℕ) : ℝ) ≤ ε}

/-- **Acylindricity of `Γ(G,A)` needs only the conjugation displacement sets.**

The two-point displacement set at `(x, y)` is the conjugate by `x` of
`conjDisplacement A ε (x⁻¹y)`, and `d(x,y) = |x⁻¹y|`, so the pair of basepoints
can always be translated to `(1, x⁻¹y)`.  This is the shape the free-product
estimate takes: bound `{k : |k| ≤ ε and |t⁻¹ k t| ≤ ε}` for `|t|` large. -/
theorem isAcylindrical_cayley_of_conjDisplacement (A : Alphabet G)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (R : ℝ) (N : ℕ), ∀ t : G,
      R ≤ ((wordNorm A.carrier t : ℕ) : ℝ) →
        (conjDisplacement A ε t).Finite ∧ (conjDisplacement A ε t).ncard ≤ N) :
    IsAcylindrical G (Cayley A) := by
  intro ε hε
  obtain ⟨R, N, hRN⟩ := h ε hε
  refine ⟨R, N, ?_⟩
  intro x y hxy
  have hxyval : dist x y
      = ((wordNorm A.carrier ((Cayley.val x)⁻¹ * Cayley.val y) : ℕ) : ℝ) := rfl
  obtain ⟨hfin, hcard⟩ := hRN ((Cayley.val x)⁻¹ * Cayley.val y)
    (by rw [← hxyval]; exact hxy)
  have hinj : Function.Injective
      (fun k : G => Cayley.val x * k * (Cayley.val x)⁻¹) := by
    intro p q hpq
    have hpq' : Cayley.val x * p * (Cayley.val x)⁻¹
        = Cayley.val x * q * (Cayley.val x)⁻¹ := hpq
    exact mul_left_cancel (mul_right_cancel hpq')
  have himg : {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}
      = (fun k : G => Cayley.val x * k * (Cayley.val x)⁻¹) ''
        conjDisplacement A ε ((Cayley.val x)⁻¹ * Cayley.val y) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro g ⟨h1, h2⟩
      have hdx : dist x (g • x)
          = ((wordNorm A.carrier
              ((Cayley.val x)⁻¹ * (g * Cayley.val x)) : ℕ) : ℝ) := rfl
      have hdy : dist y (g • y)
          = ((wordNorm A.carrier
              ((Cayley.val y)⁻¹ * (g * Cayley.val y)) : ℕ) : ℝ) := rfl
      rw [hdx] at h1
      rw [hdy] at h2
      refine ⟨(Cayley.val x)⁻¹ * g * Cayley.val x, ⟨?_, ?_⟩, ?_⟩
      · have he : (Cayley.val x)⁻¹ * g * Cayley.val x
            = (Cayley.val x)⁻¹ * (g * Cayley.val x) := by group
        rw [he]
        exact h1
      · have he : ((Cayley.val x)⁻¹ * Cayley.val y)⁻¹
              * ((Cayley.val x)⁻¹ * g * Cayley.val x)
              * ((Cayley.val x)⁻¹ * Cayley.val y)
            = (Cayley.val y)⁻¹ * (g * Cayley.val y) := by group
        rw [he]
        exact h2
      · show Cayley.val x * ((Cayley.val x)⁻¹ * g * Cayley.val x)
            * (Cayley.val x)⁻¹ = g
        group
    · rintro g ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show ((wordNorm A.carrier ((Cayley.val x)⁻¹
            * ((Cayley.val x * k * (Cayley.val x)⁻¹)
              * Cayley.val x)) : ℕ) : ℝ) ≤ ε
        have he : (Cayley.val x)⁻¹
            * ((Cayley.val x * k * (Cayley.val x)⁻¹) * Cayley.val x) = k := by
          group
        rw [he]
        exact hk1
      · show ((wordNorm A.carrier ((Cayley.val y)⁻¹
            * ((Cayley.val x * k * (Cayley.val x)⁻¹)
              * Cayley.val y)) : ℕ) : ℝ) ≤ ε
        have he : (Cayley.val y)⁻¹
              * ((Cayley.val x * k * (Cayley.val x)⁻¹) * Cayley.val y)
            = ((Cayley.val x)⁻¹ * Cayley.val y)⁻¹ * k
              * ((Cayley.val x)⁻¹ * Cayley.val y) := by group
        rw [he]
        exact hk2
  rw [himg]
  exact ⟨hfin.image _,
    le_trans (le_of_eq (Set.ncard_image_of_injective _ hinj)) hcard⟩

end Conj

/-! ## 4.  What the free product input still owes -/

/-- **The acylindricity clause of `HullSC.FreeProductUnionGeometryStatement`,
in its conjugation form.**

`isAcylindrical_cayley_of_conjDisplacement` reduces the clause to this: for the
union alphabet of two Hull generating sets, and for `t` of large union word
length, the set of `k` that are short and stay short after conjugation by `t` is
finite with a bound depending only on `ε`.  This is the tree-of-spaces crossing
estimate, and it is what the lane still owes. -/
theorem freeProductUnionGeometryStatement_of_conjDisplacement
    (hconj : ∀ (E H : Type) [Group E] [Group H] (A : HullGeneratingSet E)
      (B : HullGeneratingSet H) (ε : ℝ), 0 < ε →
        ∃ (R : ℝ) (N : ℕ), ∀ t : Monoid.Coprod E H,
          R ≤ ((wordNorm (HullSC.unionAlphabet A.alphabet B.alphabet).carrier
                t : ℕ) : ℝ) →
            (conjDisplacement (HullSC.unionAlphabet A.alphabet B.alphabet)
                ε t).Finite ∧
              (conjDisplacement (HullSC.unionAlphabet A.alphabet B.alphabet)
                ε t).ncard ≤ N)
    (hHull : ∀ (H : Type) [Group H], Infinite H →
      GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
        HasKazhdanPropertyT.{0, 0} H → Nonempty (HullGeneratingSet H)) :
    HullSC.FreeProductUnionGeometryStatement := by
  refine freeProductUnionGeometryStatement_of ?_ hHull
  intro E H instE instH A B
  letI := instE
  letI := instH
  exact isAcylindrical_cayley_of_conjDisplacement
    (HullSC.unionAlphabet A.alphabet B.alphabet) (hconj E H A B)

end HullSCUnionGeometry
end GroupApproximation
