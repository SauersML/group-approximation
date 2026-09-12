import GroupApproximation.Analysis.ShulmanFillNormingBlockLimit

/-!
# The doubled `𝒟` data

Shulman's `𝒟` is built from contractive `*`-homomorphisms `ι n : A n → B(H)`
with `ι n (1) → 1` strongly.  Its `M₂` amplification is built from the same
data at the doubled models `M₂(A n)` acting on the block space `H ⊕ H`:

    `ι' n := hBlockOp ∘ (entrywise ι n)` .

Two of the three clauses are free.  `ι' n` is a `*`-homomorphism because both
factors are, and it is contractive because a `*`-homomorphism of C-star
algebras is — no block-norm computation is needed, which is the whole reason
`Analysis/ShulmanFillNormingBlockHom` bundles `hBlockOp` as a homomorphism
before anything else happens.  Only `hone` has content, and it is the entrywise
statement `ι n (1) → 1` transported through
`tendsto_hBlockOp_of_coord`.

`Analysis/ShulmanFillNormingDoubledFlip` then exhibits the flip as a unitary of
the doubled `𝒟`, which is what
`Analysis/ShulmanFillNormingConjugationLift.conjugate` consumes.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section DoubledData

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
-- Mathlib assembles `CStarAlgebra (CStarMatrix I I K)` out of the positivity
-- order of `K`, and this repository keeps that order local rather than global
-- (`Analysis/CStarMatrixTwo`, `Analysis/CStarMatrixTwoCorner`).  Carrying it as
-- a binder is what lets the doubled models be C-star algebras downstream; a
-- consumer discharges both with `CStarAlgebra.spectralOrder` and
-- `CStarAlgebra.spectralOrderedRing`.
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The doubled models `M₂(A n)`. -/
abbrev DoubledModel (A : ℕ → Type) [∀ n, CStarAlgebra (A n)] (n : ℕ) : Type :=
  CStarMatrix (Fin 2) (Fin 2) (A n)

/-- **The doubled embedding** `M₂(A n) → B(H ⊕ H)`: apply `ι n` entrywise, then
read the matrix as one operator on the block space. -/
def doubledIota (n : ℕ) :
    DoubledModel A n →⋆ₙₐ[ℂ] (BlockSpace H 2 →L[ℂ] BlockSpace H 2) :=
  (hBlockOpHom (E := H) (n := 2)).toNonUnitalStarAlgHom.comp
    (CStarMatrix.mapₙₐ (ι n))

omit [∀ n, StarOrderedRing (A n)] [(n : ℕ) → PartialOrder (A n)] in
theorem doubledIota_apply (n : ℕ) (X : DoubledModel A n) :
    doubledIota ι n X = hBlockOp (CStarMatrix.mapₙₐ (ι n) X) := rfl

omit [∀ n, StarOrderedRing (A n)] [(n : ℕ) → PartialOrder (A n)] in
theorem mapₙₐ_entry (n : ℕ) (X : DoubledModel A n) (i j : Fin 2) :
    (CStarMatrix.mapₙₐ (ι n) X) i j = ι n (X i j) := rfl

/-- **The doubled embedding is contractive.**  It is a `*`-homomorphism of
C-star algebras, and those are contractive; nothing about the block norm is
used. -/
theorem doubled_norm_le (n : ℕ) (X : DoubledModel A n) :
    ‖doubledIota ι n X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (doubledIota ι n) X

omit [∀ (n : ℕ), StarOrderedRing (A n)] [(n : ℕ) → PartialOrder (A n)] in
/-- **The doubled units exhaust the block space.**  Entrywise the unit of
`M₂(A n)` is `ι n (1)` on the diagonal and `0` off it, so the transported
convergence is `ι n (1) → 1` in each coordinate. -/
theorem doubled_hone
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (v : BlockSpace H 2) :
    Tendsto (fun n ↦ doubledIota ι n (1 : DoubledModel A n) v) atTop (𝓝 v) := by
  have hentry : ∀ (i j : Fin 2) (x : H),
      Tendsto (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
          (1 : DoubledModel A n) i j) x) atTop
        (𝓝 (((1 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) x)) := by
    intro i j x
    by_cases hij : i = j
    · subst hij
      have hL : ∀ n : ℕ, ((CStarMatrix.mapₙₐ (ι n))
          (1 : DoubledModel A n) i i) x = ι n (1 : A n) x := by
        intro n
        rw [mapₙₐ_entry, CStarMatrix.one_apply_eq]
      have hR : ((1 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i i) x = x := by
        rw [CStarMatrix.one_apply_eq,
          _root_.one_apply_eq_self]
      simp only [hL, hR]
      exact hone x
    · have hL : ∀ n : ℕ, ((CStarMatrix.mapₙₐ (ι n))
          (1 : DoubledModel A n) i j) x = 0 := by
        intro n
        rw [mapₙₐ_entry, CStarMatrix.one_apply_ne hij,
          map_zero, _root_.zero_apply]
      have hR : ((1 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) x = 0 := by
        rw [CStarMatrix.one_apply_ne hij,
          _root_.zero_apply]
      simp only [hL, hR]
      exact tendsto_const_nhds
  have hlim := tendsto_hBlockOp_of_coord hentry v
  rwa [hBlockOp_one, _root_.one_apply_eq_self] at hlim

end DoubledData

end

end ShulmanFill
end GroupApproximation
