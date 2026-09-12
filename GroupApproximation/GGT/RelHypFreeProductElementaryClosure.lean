import GroupApproximation.GGT.RelHypOsinTheorem24Verbatim
import GroupApproximation.GGT.HullSCUnionGeometryLongSyllable

/-!
# `E_G(g)` for `g` in a factor of a free product stays in that factor

The suitability hypothesis of Osin's Theorem 2.4
(`GGT/RelHypOsinTheorem24Verbatim.IsSuitableSubgroup`) asks, at the
Fournier-Facio pair `(U ∗ H₀, U)` with witnesses `f₁, f₂ ∈ H₀`, that
`E_{U∗H₀}(f₁) ∩ E_{U∗H₀}(f₂) = {1}`.  This module performs the step that makes
that a question about `H₀` alone: **the elementary closure of a factor element
is contained in that factor**, so the ambient free product contributes nothing.

## What this is not

An earlier scoping of this wave proposed proving `E(a) = ⟨a⟩` from `a, b`
generating a free subgroup.  **That implication is false.**  In
`G = F₂ × ℤ = ⟨a, b⟩ × ⟨z⟩` the pair `(a,1), (b,1)` is free of rank two while
the central `(1,z)` centralises everything, so it lies in `E((a,1))` and in
`E((b,1))` and the intersection is not `{1}`.  A free pair does not bound `E`;
the ambient geometry does.  What Osin uses instead is his Theorem 2.1 -- `E_G(g)`
is the unique maximal elementary subgroup containing a hyperbolic `g` of
infinite order -- together with his Lemma 2.3, and both are results of his §8.

The free-product reduction below is the part that is *not* geometric: it is word
combinatorics, it needs no hyperbolicity, and it is what separates the ambient
question from the question about the factor.  What remains after it --
`E_{H₀}(f₁) ∩ E_{H₀}(f₂) = 1` inside `H₀` -- is genuinely Theorem 2.1 and Lemma
2.3 territory, and is where the citations reappear.

## The mechanism

Two lemmas of the union-geometry chain, at the alphabet in which every element
of every factor is a letter:

* `HullSCUnionGeometry.exists_normalise_conj` splits the conjugator as
  `h = of u * h'` with the normal form of `h'` avoiding the factor of `x`, and
  absorbs `u` into `x`;
* `HullSCUnionGeometry.wordNorm_conj_single_of_fstIdx_ne` then says nothing
  cancels at either seam, so `|h'⁻¹ (of x') h'| = 2|h'| + |of x'|`.

A conjugate that lands back in the factor is a single letter, so the left side
is at most one while the right side is at least `2|h'| + 1`.  Hence `|h'| = 0`,
`h' = 1`, and `h = of u`.

Taking the factor alphabets to be **all** of each factor is what makes `|of z|`
at most one for every `z`, and costs nothing: `Set.univ` is a symmetric
generating set of any group.  The decidable-equality instances the normal-form
API needs are supplied by `classical` inside the proofs and kept out of the
statements, for the reason `Sofic/OsinWeightedMetric.isPowerTorsionFree_coprodI`
records at its own copy.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductUnionNorm

/-! ## 1.  The whole-factor alphabet -/

section Factor

variable {ι : Type} {G : ι → Type} [∀ i, Group (G i)]

/-- The alphabet in which every element of every factor is a letter. -/
def fullFactorAlphabet (G : ι → Type) [∀ i, Group (G i)] : ∀ i, Set (G i) :=
  fun _ => Set.univ

theorem isSymmetricGeneratingSet_fullFactorAlphabet :
    ∀ i, IsSymmetricGeneratingSet (fullFactorAlphabet G i) :=
  fun _ => ⟨fun x _ => Set.mem_univ x⁻¹, Subgroup.closure_univ⟩

/-- Every single syllable is a letter, so its norm is at most one. -/
theorem wordNorm_of_le_one {i : ι} (z : G i) :
    wordNorm (unionCarrier (fullFactorAlphabet G)) (CoprodI.of z : CoprodI G)
      ≤ 1 :=
  wordNorm_le_one_of_mem (mem_unionCarrier_of _ (Set.mem_univ z))

/-- A nonidentity element of a factor is a nonempty word. -/
theorem one_le_wordNorm_of {i : ι} {z : G i} (hz : z ≠ 1) :
    1 ≤ wordNorm (unionCarrier (fullFactorAlphabet G)) (CoprodI.of z : CoprodI G) := by
  rcases Nat.eq_zero_or_pos
    (wordNorm (unionCarrier (fullFactorAlphabet G)) (CoprodI.of z : CoprodI G))
    with h0 | hpos
  · exfalso
    have hone : (CoprodI.of z : CoprodI G) = 1 :=
      (wordNorm_eq_zero_iff
        (isSymmetricGeneratingSet_unionCarrier
          isSymmetricGeneratingSet_fullFactorAlphabet) _).mp h0
    exact hz (CoprodI.of_injective i (hone.trans
      (map_one (CoprodI.of : G i →* CoprodI G)).symm))
  · exact hpos

end Factor

/-! ## 2.  A conjugate that lands in the factor has its conjugator there -/

/-- **The conjugator of a factor element into a factor element lies in the
factor.**

If `h⁻¹ (of x) h = of y` with `x ≠ 1`, then `h` is itself a single syllable of
the same factor.  No hypothesis on `y`: were it trivial, `of x` would be too. -/
theorem exists_factor_of_conj_single {ι : Type} {G : ι → Type}
    [∀ i, Group (G i)] {i : ι} {x y : G i} (hx : x ≠ 1) {h : CoprodI G}
    (hconj : h⁻¹ * (CoprodI.of x : CoprodI G) * h = CoprodI.of y) :
    ∃ z : G i, (CoprodI.of z : CoprodI G) = h := by
  haveI : DecidableEq ι := Classical.decEq _
  haveI : ∀ i, DecidableEq (G i) := fun _ => Classical.decEq _
  obtain ⟨u, h', hsplit, hidx, hxu⟩ :=
    HullSCUnionGeometry.exists_normalise_conj hx h
  refine ⟨u, ?_⟩
  have hzero : wordNorm (unionCarrier (fullFactorAlphabet G)) h' = 0 := by
    have hrewrite : h⁻¹ * (CoprodI.of x : CoprodI G) * h
        = h'⁻¹ * (CoprodI.of (u⁻¹ * x * u) : CoprodI G) * h' := by
      rw [hsplit]
      simp only [map_mul, map_inv]
      group
    have hkey : wordNorm (unionCarrier (fullFactorAlphabet G))
        (h'⁻¹ * (CoprodI.of (u⁻¹ * x * u) : CoprodI G) * h')
        = 2 * wordNorm (unionCarrier (fullFactorAlphabet G)) h'
          + wordNorm (unionCarrier (fullFactorAlphabet G))
            (CoprodI.of (u⁻¹ * x * u) : CoprodI G) :=
      HullSCUnionGeometry.wordNorm_conj_single_of_fstIdx_ne
        isSymmetricGeneratingSet_fullFactorAlphabet hxu hidx
    have hle : wordNorm (unionCarrier (fullFactorAlphabet G))
        (h'⁻¹ * (CoprodI.of (u⁻¹ * x * u) : CoprodI G) * h') ≤ 1 := by
      rw [← hrewrite, hconj]
      exact wordNorm_of_le_one y
    have hone : 1 ≤ wordNorm (unionCarrier (fullFactorAlphabet G))
        (CoprodI.of (u⁻¹ * x * u) : CoprodI G) := one_le_wordNorm_of hxu
    omega
  have hh' : h' = 1 :=
    (wordNorm_eq_zero_iff
      (isSymmetricGeneratingSet_unionCarrier
        isSymmetricGeneratingSet_fullFactorAlphabet) _).mp hzero
  rw [hsplit, hh', mul_one]

/-! ## 3.  The reduction of `E` -/

/-- **`E_{∗Gⱼ}(of x) ⊆ Gᵢ` for `x` of infinite order in the factor `Gᵢ`.**

The free-product half of the suitability question.  What is left after it is a
statement about the factor alone, and that half is Osin's Theorem 2.1 together
with his Lemma 2.3. -/
theorem exists_factor_of_mem_osinElementaryClosure {ι : Type} {G : ι → Type}
    [∀ i, Group (G i)] {i : ι} {x : G i} (hx : ∀ n : ℕ, 0 < n → x ^ n ≠ 1)
    {h : CoprodI G}
    (hh : h ∈ osinElementaryClosure (CoprodI.of x : CoprodI G)) :
    ∃ z : G i, (CoprodI.of z : CoprodI G) = h := by
  obtain ⟨n, hn, hcase⟩ := hh
  have hxn : x ^ n ≠ 1 := hx n hn
  rcases hcase with hc | hc
  · rw [← map_pow] at hc
    exact exists_factor_of_conj_single (y := x ^ n) hxn hc
  · rw [← map_pow, ← map_inv] at hc
    exact exists_factor_of_conj_single (y := (x ^ n)⁻¹) hxn hc

end RelHyp
end GGT
end GroupApproximation
