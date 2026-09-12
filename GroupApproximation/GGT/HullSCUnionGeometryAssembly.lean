import GroupApproximation.GGT.HullSCUnionGeometryShortBranch
import GroupApproximation.GGT.HullSCUnionGeometryVirtuallyCyclic

/-!
# `HullSC.FreeProductUnionGeometryStatement`, unconditionally

Both clauses are now available: hyperbolicity of `Γ(E ∗ H, A ⊔ B)` is
`exists_isHyperbolicSpace_cayley_unionAlphabet`, and acylindricity of the
translation action is what this module assembles.

## The three steps

* `exists_famDisplacement_bound` makes the two factors' acylindricity uniform
  over the two-element index of `Higman.Amalgam.fam`: `max` of the two radii and
  `max` of the two counts.
* `isAcylindrical_unionAlphabet` transports `exists_conjDisplacement_bound` from
  `CoprodI (Amalgam.fam E H)` to `E ∗ H` along `Higman.coprodEquiv`.  The
  isomorphism carries the union alphabet to the union alphabet, so it preserves
  word length (`HullSC.wordNorm_of_mulEquiv`), hence carries each conjugation
  displacement set onto the other; `Set.ncard_image_of_injective` moves the
  count.
* `freeProductUnionGeometryStatement_unconditional` feeds that to
  `freeProductUnionGeometryStatement_of_acylindricalUnion`, whose only
  hypothesis it was.

## What the count is

For `ε` the bound is `max ((⌊ε⌋₊ + 2) ^ 2) (max N_E N_H)`: the crossing estimate
where `t` has many syllables, and the factor's own two-point count where `t` has
few syllables and one long letter.  No ball of `A ⊔ B` is ever enumerated ---
Hull's alphabets are infinite, and every element of every displacement set is
named by data read off `t` together with one letter of one factor.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

section Assembly

variable {E H : Type} [Group E] [Group H]

/-- **The two factors' displacement bounds, made uniform.**  The index is
`Bool`, so `max` of the two radii and of the two counts serves both. -/
theorem exists_famDisplacement_bound (A : HullGeneratingSet E)
    (B : HullGeneratingSet H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R₀ : ℝ) (N₀ : ℕ), ∀ (i : Bool) (τ : Higman.Amalgam.fam E H i),
      R₀ ≤ ((wordNorm (famCarrier A.alphabet.carrier B.alphabet.carrier i)
        τ : ℕ) : ℝ) →
        {γ : Higman.Amalgam.fam E H i |
            ((wordNorm (famCarrier A.alphabet.carrier B.alphabet.carrier i)
              γ : ℕ) : ℝ) ≤ ε ∧
            ((wordNorm (famCarrier A.alphabet.carrier B.alphabet.carrier i)
              (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.Finite ∧
          {γ : Higman.Amalgam.fam E H i |
            ((wordNorm (famCarrier A.alphabet.carrier B.alphabet.carrier i)
              γ : ℕ) : ℝ) ≤ ε ∧
            ((wordNorm (famCarrier A.alphabet.carrier B.alphabet.carrier i)
              (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard ≤ N₀ := by
  obtain ⟨RE, NE, hE⟩ :=
    exists_factorDisplacement_bound A.alphabet A.acylindrical hε
  obtain ⟨RH, NH, hH⟩ :=
    exists_factorDisplacement_bound B.alphabet B.acylindrical hε
  refine ⟨max RE RH, max NE NH, ?_⟩
  intro i
  cases i with
  | false =>
      intro τ hτ
      obtain ⟨hfin, hcard⟩ := hE τ (le_trans (le_max_left _ _) hτ)
      exact ⟨hfin, le_trans hcard (le_max_left _ _)⟩
  | true =>
      intro τ hτ
      obtain ⟨hfin, hcard⟩ := hH τ (le_trans (le_max_right _ _) hτ)
      exact ⟨hfin, le_trans hcard (le_max_right _ _)⟩

/-- **The translation action of `E ∗ H` on the union alphabet is
acylindrical.** -/
theorem isAcylindrical_unionAlphabet (A : HullGeneratingSet E)
    (B : HullGeneratingSet H) :
    IsAcylindrical (Monoid.Coprod E H)
      (Cayley (HullSC.unionAlphabet A.alphabet B.alphabet)) := by
  classical
  letI : ∀ b : Bool, DecidableEq (Higman.Amalgam.fam E H b) :=
    fun b => Classical.decEq (Higman.Amalgam.fam E H b)
  refine isAcylindrical_cayley_of_conjDisplacement _ ?_
  intro ε hε
  have hfam : ∀ b : Bool,
      IsSymmetricGeneratingSet (famCarrier A.alphabet.carrier B.alphabet.carrier b) :=
    isSymmetricGeneratingSet_famCarrier A.alphabet.symmetricGenerating
      B.alphabet.symmetricGenerating
  -- the union alphabet, read on `CoprodI (Amalgam.fam E H)`
  let A' : Alphabet (CoprodI (Higman.Amalgam.fam E H)) :=
    ⟨unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier),
      isSymmetricGeneratingSet_unionCarrier hfam⟩
  -- the isomorphism preserves word length
  have hmem : ∀ x ∈ HullSC.UnionCarrier A.alphabet B.alphabet,
      Higman.coprodEquiv x
        ∈ unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier) := by
    intro x hx
    rcases HullSC.mem_unionCarrier.mp hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨false, a, ha, (coprodEquiv_inl a).symm⟩
    · exact ⟨true, b, hb, (coprodEquiv_inr b).symm⟩
  have hmem' : ∀ x ∈ unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier),
      Higman.coprodEquiv.symm x ∈ HullSC.UnionCarrier A.alphabet B.alphabet := by
    rintro x ⟨i, a, ha, rfl⟩
    cases i with
    | false =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inl ⟨a, ha, (coprodEquiv_symm_false a).symm⟩)
    | true =>
        exact HullSC.mem_unionCarrier.mpr
          (Or.inr ⟨a, ha, (coprodEquiv_symm_true a).symm⟩)
  have hnorm : ∀ w : Monoid.Coprod E H,
      wordNorm (unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier))
          (Higman.coprodEquiv w)
        = wordNorm (HullSC.UnionCarrier A.alphabet B.alphabet) w :=
    HullSC.wordNorm_of_mulEquiv
      (HullSC.unionAlphabet A.alphabet B.alphabet).symmetricGenerating
      (isSymmetricGeneratingSet_unionCarrier hfam)
      (Higman.coprodEquiv (G := E) (H := H)) hmem hmem'
  obtain ⟨R₀, N₀, hfac⟩ := exists_famDisplacement_bound A B hε
  obtain ⟨R, N, hRN⟩ :=
    exists_conjDisplacement_bound hfam (A := A') rfl hε hfac
  refine ⟨R, N, ?_⟩
  intro t hRt
  have hRt' : R ≤ ((wordNorm
      (unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier))
        (Higman.coprodEquiv t) : ℕ) : ℝ) := by
    rw [hnorm t]
    exact hRt
  obtain ⟨hfin, hcard⟩ := hRN (Higman.coprodEquiv t) hRt'
  -- the two displacement sets correspond
  have hmemD : ∀ k : Monoid.Coprod E H,
      k ∈ conjDisplacement (HullSC.unionAlphabet A.alphabet B.alphabet) ε t
        ↔ Higman.coprodEquiv k
          ∈ conjDisplacement A' ε (Higman.coprodEquiv t) := by
    intro k
    have hmap : Higman.coprodEquiv (t⁻¹ * k * t)
        = (Higman.coprodEquiv t)⁻¹ * Higman.coprodEquiv k
          * Higman.coprodEquiv t := by
      rw [map_mul, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show ((wordNorm
            (unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier))
              (Higman.coprodEquiv k) : ℕ) : ℝ) ≤ ε
        rw [hnorm k]
        exact h1
      · show ((wordNorm
            (unionCarrier (famCarrier A.alphabet.carrier B.alphabet.carrier))
              ((Higman.coprodEquiv t)⁻¹ * Higman.coprodEquiv k
                * Higman.coprodEquiv t) : ℕ) : ℝ) ≤ ε
        rw [← hmap, hnorm (t⁻¹ * k * t)]
        exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show ((wordNorm (HullSC.UnionCarrier A.alphabet B.alphabet) k : ℕ) : ℝ)
          ≤ ε
        rw [← hnorm k]
        exact h1
      · show ((wordNorm (HullSC.UnionCarrier A.alphabet B.alphabet)
            (t⁻¹ * k * t) : ℕ) : ℝ) ≤ ε
        rw [← hnorm (t⁻¹ * k * t), hmap]
        exact h2
  have hseteq : conjDisplacement (HullSC.unionAlphabet A.alphabet B.alphabet) ε t
      = (fun x => Higman.coprodEquiv.symm x) ''
        conjDisplacement A' ε (Higman.coprodEquiv t) := by
    ext k
    constructor
    · intro hk
      exact ⟨Higman.coprodEquiv k, (hmemD k).mp hk,
        Higman.coprodEquiv.symm_apply_apply k⟩
    · rintro ⟨x, hx, rfl⟩
      refine (hmemD _).mpr ?_
      rwa [Higman.coprodEquiv.apply_symm_apply]
  rw [hseteq]
  refine ⟨hfin.image _, ?_⟩
  rw [Set.ncard_image_of_injective _ Higman.coprodEquiv.symm.injective]
  exact hcard

/-- **Hull's free-product geometry, unconditionally.**  Both clauses of
`HullSC.FreeProductUnionGeometryStatement` are proved: the Cayley graph of the
union alphabet is hyperbolic, and the translation action on it is
acylindrical. -/
theorem freeProductUnionGeometryStatement_unconditional :
    HullSC.FreeProductUnionGeometryStatement := by
  refine freeProductUnionGeometryStatement_of_acylindricalUnion ?_
  intro E H instE instH A B
  letI := instE
  letI := instH
  exact isAcylindrical_unionAlphabet A B

end Assembly

end HullSCUnionGeometry
end GroupApproximation
