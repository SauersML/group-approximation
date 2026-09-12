import GroupApproximation.Analysis.CStarMatrixTwo
import GroupApproximation.Analysis.UniversalCStarAmalgam
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceSetupUniversal
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences

/-!
# `thm:hnn-permanence`, Step 1: `U` embeds in an amalgamated free product

This module formalizes the paragraph

> *Step 1: `U` embeds in an amalgamated free product.*  Let `C = B₀ ⊕ B₁`,
> `A₁ = M₂(D)`, and `A₂ = M₂(B₀)`, with the unital inclusions
> `ι_A(c₀, c₁) = diag(c₀, c₁) ∈ A₁`, `ι_B(c₀, c₁) = diag(c₀, Θ⁻¹(c₁)) ∈ A₂`,
> and let `P = A₁ *_C A₂` be the full amalgamated free product, in which `A₁`
> and `A₂` embed [Shulman, Section 2.1].  Ueda proved that the universal HNN
> extension is a full corner of exactly this amalgamated free product
> [Ueda, Proposition 2.4]: for the projection `e = ι_A(1_D, 0) = ι_B(1_D, 0)`
> there is an isomorphism of `U` onto `ePe` carrying `d ∈ D` to `diag(d, 0)`
> and the unitary `u` to the partial isometry `e₁₂f₂₁` built from the matrix
> units `e_ij` of `A₁` and `f_ij` of `A₂`.  In particular `U` embeds in `P`.

The compatible corona pair `(φ_A, φ_B)` of Step 2 is constructed here as well,
because the repository's full amalgam `UniversalCStarAmalgam` is built from its
family of compatible representations, so one compatible pair is needed before
`P` can be named at all.  Step 2 itself — Shulman's MF criterion — is in
`HNNPermanenceShulman`.

Two printed sentences of the paragraph are *proved* rather than cited: `A₁` and
`A₂` embed in `P` (the repository's
`manuscriptSentence_ce5f1d31a90e_factorMapsInjective`, applied to the corona
pair), and `e₁₂f₂₁` is a unitary of the corner `ePe` (the repository's
`manuscriptSentence_6e8a0c1082a2_cornerWordUnitary`, applied to the matrix
units of `A₁` and `A₂`).  Only Ueda's Proposition 2.4 is a literature input.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences

noncomputable section

/-! ## Two elementary constructions on products and two-by-two matrices -/

/-- The direct sum `E ⊕ F` of two C-star algebras is a C-star algebra.

The manuscript's amalgamated algebra is `C = B₀ ⊕ B₁`, and
`CStarAmalgamRepresentation` asks for its `Semiring`, `Algebra` and `Star`
structures to arrive through a `CStarAlgebra` instance.  Without this instance
the product carries only `Prod.instSemiring` and friends, and the two cannot be
unified. -/
noncomputable instance prodCStarAlgebra {E F : Type} [CStarAlgebra E]
    [CStarAlgebra F] : CStarAlgebra (E × F) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The two-by-two matrices over a C-star algebra form a C-star algebra.

Mathlib builds this from the positivity order of `K`, so `PartialOrder K` and
`StarOrderedRing K` have to be available while the instance is assembled.  They
are introduced by `letI` *inside this proof* rather than as ambient instances:
as ambient instances they enter the `Semiring`/`StarRing` paths of `K` itself
and make later goals ill-typed at `instances` transparency. -/
noncomputable instance matrixTwoCStarAlgebra {K : Type} [CStarAlgebra K] :
    CStarAlgebra (CStarMatrix (Fin 2) (Fin 2) K) := by
  letI : PartialOrder K := CStarAlgebra.spectralOrder K
  letI : StarOrderedRing K := CStarAlgebra.spectralOrderedRing K
  exact inferInstance

/-- The product of two star-algebra homomorphisms with a common target. -/
def prodStarAlgHom {E F K : Type} [CStarAlgebra E] [CStarAlgebra F]
    [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (g : F →⋆ₐ[ℂ] K) :
    E × F →⋆ₐ[ℂ] K × K where
  toFun p := (f p.1, g p.2)
  map_one' := by
    show (f (1 : E), g (1 : F)) = ((1 : K), (1 : K))
    rw [map_one, map_one]
  map_mul' p q := by
    show (f (p.1 * q.1), g (p.2 * q.2)) = (f p.1 * f q.1, g p.2 * g q.2)
    rw [map_mul, map_mul]
  map_zero' := by
    show (f (0 : E), g (0 : F)) = ((0 : K), (0 : K))
    rw [map_zero, map_zero]
  map_add' p q := by
    show (f (p.1 + q.1), g (p.2 + q.2)) = (f p.1 + f q.1, g p.2 + g q.2)
    rw [map_add, map_add]
  commutes' r := by
    have hf : f (algebraMap ℂ E r) = algebraMap ℂ K r := f.commutes r
    have hg : g (algebraMap ℂ F r) = algebraMap ℂ K r := g.commutes r
    show (f (algebraMap ℂ E r), g (algebraMap ℂ F r)) =
      (algebraMap ℂ K r, algebraMap ℂ K r)
    rw [hf, hg]
  map_star' p := by
    show (f (star p.1), g (star p.2)) = (star (f p.1), star (g p.2))
    rw [map_star, map_star]

@[simp] theorem prodStarAlgHom_apply {E F K : Type} [CStarAlgebra E]
    [CStarAlgebra F] [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (g : F →⋆ₐ[ℂ] K)
    (p : E × F) : prodStarAlgHom f g p = (f p.1, g p.2) :=
  rfl

/-- The printed diagonal inclusion `(c₀, c₁) ↦ diag(f c₀, g c₁)`. -/
def diagonalPairHom {E F K : Type} [CStarAlgebra E] [CStarAlgebra F]
    [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (g : F →⋆ₐ[ℂ] K) :
    E × F →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) K :=
  cStarDiagonalTwoHom.comp (prodStarAlgHom f g)

@[simp] theorem diagonalPairHom_apply {E F K : Type} [CStarAlgebra E]
    [CStarAlgebra F] [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (g : F →⋆ₐ[ℂ] K)
    (p : E × F) :
    diagonalPairHom f g p = cStarDiagonalTwo (f p.1) (g p.2) :=
  rfl

/-- The entrywise two-by-two amplification of a unital star-algebra
homomorphism.  Its non-unital fields are those of `CStarMatrix.mapₙₐ`. -/
def matrixTwoMap {E K : Type} [CStarAlgebra E] [CStarAlgebra K]
    (f : E →⋆ₐ[ℂ] K) :
    CStarMatrix (Fin 2) (Fin 2) E →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) K where
  toFun := fun M ↦ (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
    CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) K) M
  map_one' := by
    ext i j
    change f ((1 : CStarMatrix (Fin 2) (Fin 2) E) i j) =
      (1 : CStarMatrix (Fin 2) (Fin 2) K) i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' M N :=
    map_mul (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
      CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
        CStarMatrix (Fin 2) (Fin 2) K) M N
  map_zero' :=
    map_zero (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
      CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
        CStarMatrix (Fin 2) (Fin 2) K)
  map_add' M N :=
    map_add (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
      CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
        CStarMatrix (Fin 2) (Fin 2) K) M N
  commutes' r := by
    have hone : (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
        CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
          CStarMatrix (Fin 2) (Fin 2) K) 1 = 1 := by
      ext i j
      change f ((1 : CStarMatrix (Fin 2) (Fin 2) E) i j) =
        (1 : CStarMatrix (Fin 2) (Fin 2) K) i j
      fin_cases i <;> fin_cases j <;> simp
    show (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
        CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
          CStarMatrix (Fin 2) (Fin 2) K)
        (algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) E) r) =
      algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) K) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      map_smul, hone]
  map_star' M :=
    map_star (CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom :
      CStarMatrix (Fin 2) (Fin 2) E →⋆ₙₐ[ℂ]
        CStarMatrix (Fin 2) (Fin 2) K) M

@[simp] theorem matrixTwoMap_entry {E K : Type} [CStarAlgebra E]
    [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K)
    (M : CStarMatrix (Fin 2) (Fin 2) E) (i j : Fin 2) :
    matrixTwoMap f M i j = f (M i j) :=
  rfl

theorem matrixTwoMap_diagonal {E K : Type} [CStarAlgebra E] [CStarAlgebra K]
    (f : E →⋆ₐ[ℂ] K) (x y : E) :
    matrixTwoMap f (cStarDiagonalTwo x y) = cStarDiagonalTwo (f x) (f y) := by
  ext i j
  change f (cStarDiagonalTwo x y i j) = cStarDiagonalTwo (f x) (f y) i j
  fin_cases i <;> fin_cases j <;> simp

theorem matrixTwoMap_injective {E K : Type} [CStarAlgebra E] [CStarAlgebra K]
    {f : E →⋆ₐ[ℂ] K} (hf : Function.Injective f) :
    Function.Injective (matrixTwoMap f) := by
  intro M N hMN
  ext i j
  exact hf (congrArg (fun P : CStarMatrix (Fin 2) (Fin 2) K ↦ P i j) hMN)

/-- Conjugating a two-by-two diagonal matrix is diagonal conjugation. -/
theorem conj_cStarDiagonalTwo {K : Type} [CStarAlgebra K] (u v a b : K) :
    cStarDiagonalTwo u v * cStarDiagonalTwo a b *
        star (cStarDiagonalTwo u v) =
      cStarDiagonalTwo (u * a * star u) (v * b * star v) := by
  have key : cStarDiagonalTwoHom
        (((u, v) : K × K) * ((a, b) : K × K) * star ((u, v) : K × K)) =
      cStarDiagonalTwoHom ((u, v) : K × K) *
          cStarDiagonalTwoHom ((a, b) : K × K) *
        star (cStarDiagonalTwoHom ((u, v) : K × K)) := by
    rw [map_mul, map_mul, map_star]
  exact key.symm

/-- Two-by-two diagonal matrices multiply componentwise. -/
theorem cStarDiagonalTwo_mul {K : Type} [CStarAlgebra K] (a b c d : K) :
    cStarDiagonalTwo a b * cStarDiagonalTwo c d =
      cStarDiagonalTwo (a * c) (b * d) :=
  (map_mul cStarDiagonalTwoHom ((a, b) : K × K) ((c, d) : K × K)).symm

/-- The star of a two-by-two diagonal matrix is componentwise. -/
theorem star_cStarDiagonalTwo {K : Type} [CStarAlgebra K] (a b : K) :
    star (cStarDiagonalTwo a b) = cStarDiagonalTwo (star a) (star b) :=
  (map_star cStarDiagonalTwoHom ((a, b) : K × K)).symm

/-- The diagonal matrix with both entries `1` is the unit. -/
theorem cStarDiagonalTwo_one {K : Type} [CStarAlgebra K] :
    cStarDiagonalTwo (1 : K) 1 = 1 :=
  map_one cStarDiagonalTwoHom

theorem cStarDiagonalTwo_one_zero {K : Type} [CStarAlgebra K] :
    cStarDiagonalTwo (1 : K) 0 = cStarMatrixUnitTwo 0 0 (1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cStarDiagonalTwo_zero_one {K : Type} [CStarAlgebra K] :
    cStarDiagonalTwo (0 : K) 1 = cStarMatrixUnitTwo 1 1 (1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
