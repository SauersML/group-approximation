import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingProperIsometry
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingStrictness
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# The proper isometry at every rank `n ≥ 2`

`non_mf_groups_exist.tex`, `cor:one-sided-ring-maximal`: the printed corollary
now asserts the proper isometry for `n ≥ 4` unconditionally on "not directly
finite", and for `n ≥ 2` under Theorem B's hypothesis.  This module carries the
second form.

## The route

`FullDefectRingProperIsometry.properIsometry_of_strictCompression` turns a
property-`(T)` subgroup strictly compressed by one element into the whole
printed conclusion, at any group whatever.  So the only thing needed at rank
two is such a pair, and it is obtained by **transporting the rank-four pair
along an injective homomorphism**:

* `FullDefectRingStrictness.manuscriptOneSidedCompressorStrictContainment`
  supplies `Γ₄ ≤ EL₄(R)` and `u₄` with `u₄Γ₄u₄⁻¹ ⊊ Γ₄`;
* the descent homomorphism `Ψ` of `Leavitt.RankDescentEmbedding` is **injective**,
  because `ȷ` is (`T_i ȷ(A) S_j = A_ij`) and `x ↦ diag(x,1)` is;
* an injective homomorphism carries a strictly compressed property-`(T)`
  subgroup to a strictly compressed property-`(T)` subgroup, which is
  `strictCompression_map` below.

Rank `n ≥ 3` is then reached from rank two by the same transport along the
block embedding, which is injective for the same reason `elementaryStabilization`
is.  So one lemma serves both steps and there is no case analysis on `n`
beyond writing `n = 2 + k`.

## Where the hypothesis is spent

Theorem B's hypothesis gives a properly infinite unit, hence `w₀v₀ = 1`; and it
gives `v₀w₀ ≠ 1` whenever `R` is nonzero, because `e = 1 - v₀w₀` is full and a
full idempotent in a nonzero ring is nonzero.  That is exactly the "not
directly finite" input the rank-four statement asks for, so the rank-four
theorem applies and nothing further about `R` is used.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRankTwo

open RankDescent
open OneSidedCompressor

/-! ## Transport of a strict compression along an injective homomorphism -/

/-- **An injective homomorphism carries a strictly compressed property-`(T)`
subgroup to one of the same kind.**  Both halves are formal: property `(T)`
passes to a homomorphic image, and `Subgroup.map` of an injective map is
strictly monotone. -/
theorem strictCompression_map {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (Γ : Subgroup G) (u : G)
    (hT : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (hlt : Γ.map (MulAut.conj u).toMonoidHom < Γ) :
    HasKazhdanPropertyT.{0, 0} ↥(Γ.map f) ∧
      (Γ.map f).map (MulAut.conj (f u)).toMonoidHom < Γ.map f := by
  constructor
  · have hmem : ∀ x : ↥Γ, f (x : G) ∈ Γ.map f := fun x ↦ ⟨x, x.2, rfl⟩
    have hsurj : Function.Surjective
        ((f.comp Γ.subtype).codRestrict (Γ.map f) hmem) := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact HasKazhdanPropertyT.of_surjective _ hsurj hT
  · have hcomm : (Γ.map (MulAut.conj u).toMonoidHom).map f
        = (Γ.map f).map (MulAut.conj (f u)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj]
    rw [← hcomm]
    refine lt_of_le_of_ne (Subgroup.map_mono hlt.le) ?_
    intro heq
    exact hlt.ne (Subgroup.map_injective hf heq)

/-! ## Injectivity of the descent homomorphism -/

section Injective

variable {R : Type} [Ring R] (S T : Fin 4 → R)
  (hTS : ∀ i j, T i * S j = if i = j then 1 else 0)

theorem blockDiagHom_injective : Function.Injective (blockDiagHom R) := by
  intro x y hxy
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 0) hxy
  simpa [blockDiagHom, Matrix.single_apply, Matrix.one_apply,
    sub_eq_iff_eq_add] using h

include hTS

theorem psiUnits_injective : Function.Injective (psiUnits S T hTS) := by
  intro u v h
  apply Units.ext
  refine jMap_injective S T hTS (blockDiagHom_injective (R := R) ?_)
  exact congrArg Units.val h

theorem psi_injective : Function.Injective (psi S T hTS) := by
  intro x y h
  apply Subtype.ext
  exact psiUnits_injective S T hTS (congrArg Subtype.val h)

end Injective

theorem descent_injective {R : Type} [Ring R] (Q : ProperlyInfiniteUnit R) :
    Function.Injective (descent Q) :=
  psi_injective _ _ _

/-! ## Injectivity of the block embedding -/

theorem blockEmbed_injective (R : Type) [Ring R] (k : ℕ) :
    Function.Injective (blockEmbed R k) :=
  (elementaryReindexEquiv (R := R)
    (finSumFinEquiv : Fin 2 ⊕ Fin k ≃ Fin (2 + k))).injective.comp
      elementaryStabilization_injective

/-! ## The strict compression at every rank `n ≥ 2` -/

/-- Theorem B's hypothesis makes `R` fail to be directly finite, as soon as `R`
is nonzero: the complementary idempotent is full, and a full idempotent in a
nonzero ring is nonzero. -/
theorem not_directlyFinite_of_full {R : Type} [Ring R] [Nontrivial R]
    (s t : R) {m : ℕ} (a b : Fin m → R)
    (hab : ∑ i, a i * (1 - s * t) * b i = 1) : s * t ≠ 1 := by
  intro hst
  have hzero : (1 : R) - s * t = 0 := by rw [hst, sub_self]
  have hcon : (0 : R) = 1 := by
    rw [← hab]
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    rw [hzero, mul_zero, zero_mul]
  exact zero_ne_one hcon

/-- **The printed strict compression at every rank `n ≥ 2`**, under Theorem B's
hypothesis. -/
theorem exists_strictCompression_rankTwo {R : Type} [Ring R] [Countable R]
    [Nontrivial R] (s t : R) (hts : t * s = 1)
    {m : ℕ} (a b : Fin m → R) (hab : ∑ i, a i * (1 - s * t) * b i = 1)
    (hT : ∀ (S : Subring R), IsFinitelyGeneratedRing ↥S → ∀ (k : ℕ), 3 ≤ k →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin k) ↥S))
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Γ : Subgroup (elementaryGroup (Fin n) R))
      (u : elementaryGroup (Fin n) R),
      HasKazhdanPropertyT.{0, 0} ↥Γ ∧
        Γ.map (MulAut.conj u).toMonoidHom < Γ := by
  classical
  set P : OneSidedInverse R := ⟨s, t, hts⟩ with hP
  have hab' : ∑ i, a i * P.e * b i = 1 := hab
  set Q : ProperlyInfiniteUnit R := ofFull P a b hab' with hQ
  -- the rank-four pair
  obtain ⟨G4, u4, hT4, hlt4⟩ :=
    FullDefectRing.manuscriptOneSidedCompressorStrictContainment R s t hts
      (not_directlyFinite_of_full s t a b hab) hT 4 le_rfl
  -- transport to rank two along the injective descent homomorphism
  obtain ⟨hT2, hlt2⟩ :=
    strictCompression_map (descent Q) (descent_injective Q) G4 u4 hT4 hlt4
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  -- and along the block embedding to rank `2 + k`
  obtain ⟨hTn, hltn⟩ :=
    strictCompression_map (blockEmbed R k) (blockEmbed_injective R k)
      (G4.map (descent Q)) (descent Q u4) hT2 hlt2
  exact ⟨(G4.map (descent Q)).map (blockEmbed R k),
    blockEmbed R k (descent Q u4), hTn, hltn⟩

/-! ## The printed corollary at `n ≥ 2` -/

/-- **`cor:one-sided-ring-maximal`, first sentence, at every rank `n ≥ 2`**,
under Theorem B's hypothesis. -/
def PrintedOneSidedRingMaximalIsometryRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] [Nontrivial R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ i, a i * (1 - s * t) * b i = 1) →
      ∀ (n : ℕ), 2 ≤ n →
        (∃ v : MaximalGroupCStar (elementaryGroup (Fin n) R),
            star v * v = 1 ∧ ¬ IsUnit v) ∧
          ¬ IsDedekindFiniteMonoid
            (MaximalGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ IsStablyFiniteRing (MaximalGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ Nonempty (FaithfulTracialState
            (MaximalGroupCStar (elementaryGroup (Fin n) R))) ∧
          ¬ IsResiduallyFiniteDimensional
            (MaximalGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ HasMFEmbedding (MaximalGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ IsMFAlgebra (MaximalGroupCStar (elementaryGroup (Fin n) R))

theorem manuscriptOneSidedRingMaximalIsometryRankTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedOneSidedRingMaximalIsometryRankTwo := by
  intro R _ _ _ s t hts hfull n hn
  obtain ⟨m, a, b, hab⟩ := hfull
  obtain ⟨Γ, u, hT, hlt⟩ :=
    exists_strictCompression_rankTwo s t hts a b hab
      (fun S hfg k hk ↦ hEJZ (↥S) hfg k hk) n hn
  exact FullDefectRing.properIsometry_of_strictCompression Γ u hT hlt

end FullDefectRankTwo
end OneSidedMFRadical
end Manuscript
end GroupApproximation
