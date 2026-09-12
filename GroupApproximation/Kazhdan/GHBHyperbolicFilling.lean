import GroupApproximation.Kazhdan.GHBHyperbolic
import GroupApproximation.Kazhdan.CCKWCosetComplexLinks
import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.Meta.AxiomGuard

/-!
# The area input for the coset complex of `GHB(7)`

`GHBHyperbolicStokes.ChainFillingBound Adj Tri A` bounds the sum of an antisymmetric function
around a closed edge path `v :: l ++ [v]` by `C₀ A (|l| + 1)`, where `C₀` bounds its sums around
triangles.  This module derives it at `A = 6` from the minimal-disc layer:

* HC10 (`Systolic.exists_leastDisc_typedLinks`, over `FillingStatement` and
  `MirrorFoldStatement`): every nonconstant closed edge path bounds a triangulated disc whose
  interior vertices meet the link bound `n`;
* HC11 (`TypedCountStatement X n`): such a disc has at most `6` triangles per boundary edge;
* HC12 (`BoundarySumStatement X`): the boundary sum is at most `C₀` times the number of
  triangles.

A disc bounding `v :: l ++ [v]` has `|l| + 1` boundary edges (`faceDegree_outer_eq`), so
`|Σ| ≤ C₀ F ≤ C₀ · 6 · (|l| + 1)` (`chainFillingBound_of_leastDiscs`).

At the coset complex of `GHB(7)` the link bound is the typed girth `6, 8, 8` of
`CCKW.cosetComplex_linksLargeAt`, at the order bounds `|U₃(7)| ≤ 7³`, `|U₄(7)| ≤ 7⁴`
(`CCKW.chainFillingBound_cosetComplex`).  With the letter glue of `GHBHyperbolic.lean` this
gives `IsHyperbolicGroup (GHB 7)` over filling, folding, the typed count and boundary sums
(`GHBQuotient.isHyperbolicGroup_ghb7_of_discInputs`).  `GHBHyperbolicDiscCounts.lean`
discharges filling from simple connectivity and the zip move, and the count and sums from
`SystolicDiscCounts`.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route (hyperbolicity of `GHB(7)`); certifies no manuscript step on its
own.
-/

namespace GroupApproximation
namespace GHBHyperbolicStokes

open Systolic

universe u

variable {V : Type u}

section Statements

variable (X : TriangleComplex V)

/-- **HC11, as a named input.**  A triangulated disc whose interior vertices meet the link
bound `n` has at most `6` triangles per boundary edge. -/
def TypedCountStatement (n : V → ℕ) : Prop :=
  ∀ (γ : List V) (D : TriangulatedDisc X γ),
    (∀ w : D.map.Vertex, D.Interior w → n (D.vtx w) ≤ D.map.vertexDegree w) →
      D.innerFaceCount ≤ 6 * D.map.faceDegree D.outer

/-- **HC12, as a named input.**  An antisymmetric function whose sum around every triangle of
`X` is at most `C₀` has boundary sum at most `C₀` times the number of triangles of a disc. -/
def BoundarySumStatement : Prop :=
  ∀ (γ : List V) (D : TriangulatedDisc X γ) (I : V → V → ℤ), (∀ x y, I y x = -I x y) →
    ∀ C₀ : ℕ, (∀ x y z, X.Tri x y z → |I x y + I y z + I z x| ≤ C₀) →
      |(List.zipWith I γ γ.tail).sum| ≤ C₀ * D.innerFaceCount

end Statements

/-- A disc bounding `v :: l ++ [v]` has `|l| + 1` boundary edges. -/
theorem faceDegree_outer_eq {X : TriangleComplex V} {v : V} {l : List V}
    (D : TriangulatedDisc X (v :: l ++ [v])) : D.map.faceDegree D.outer = l.length + 1 := by
  have h := congrArg List.length D.boundary
  simp only [List.length_ofFn, List.length_append, List.length_cons, List.length_singleton] at h
  omega

/-- **The area input from least discs.**  Filling, folding, large links, the typed count and
boundary sums give the chain filling bound at constant `6`. -/
theorem chainFillingBound_of_leastDiscs {X : TriangleComplex V} {n : V → ℕ}
    (hfill : FillingStatement X) (hfold : MirrorFoldStatement X) (hL : LinksLargeAt X n)
    (hcount : TypedCountStatement X n) (hsum : BoundarySumStatement X) :
    ChainFillingBound X.G.Adj X.Tri 6 := by
  intro v l hl hne I hanti C₀ htri
  obtain ⟨D, -, hdeg⟩ := exists_leastDisc_typedLinks hfill hfold hL hl hne
  have hF : D.innerFaceCount ≤ 6 * (l.length + 1) := by
    have h := hcount _ D hdeg
    rwa [faceDegree_outer_eq D] at h
  have key : ∀ F : ℕ, F ≤ 6 * (l.length + 1) →
      (C₀ : ℤ) * F ≤ (C₀ : ℤ) * (6 : ℕ) * (l.length + 1) := by
    intro F hF
    have hF' : (F : ℤ) ≤ 6 * ((l.length : ℤ) + 1) := by exact_mod_cast hF
    have hC : (0 : ℤ) ≤ (C₀ : ℤ) := by positivity
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hF' hC]
  exact (hsum _ D I hanti C₀ htri).trans (key _ hF)

end GHBHyperbolicStokes

namespace KMSGroup
namespace CCKW

open GHBHyperbolicStokes

/-- **The area input for the coset complex of `GHB(7)`**, over filling, folding, the typed
count and boundary sums. -/
theorem chainFillingBound_cosetComplex (hfill : Systolic.FillingStatement cosetComplex)
    (hfold : Systolic.MirrorFoldStatement cosetComplex)
    (hcount : TypedCountStatement cosetComplex (fun x : Vertex => if x.1 = 0 then 6 else 8))
    (hsum : BoundarySumStatement cosetComplex) :
    ChainFillingBound cosetComplex.G.Adj cosetComplex.Tri 6 :=
  chainFillingBound_of_leastDiscs hfill hfold
    (cosetComplex_linksLargeAt card_U3_seven_le card_U4_seven_le) hcount hsum

end CCKW

namespace GHBQuotient

/-- **`GHB(7)` is hyperbolic**, over filling and folding of triangulated discs in its coset
complex, the typed count and boundary sums. -/
theorem isHyperbolicGroup_ghb7_of_discInputs (hfill : Systolic.FillingStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex)
    (hcount : GHBHyperbolicStokes.TypedCountStatement CCKW.cosetComplex
      (fun x : CCKW.Vertex => if x.1 = 0 then 6 else 8))
    (hsum : GHBHyperbolicStokes.BoundarySumStatement CCKW.cosetComplex) :
    Hyperbolic.IsHyperbolicGroup (GHB 7) :=
  isHyperbolicGroup_ghb7_of_chainFillingBound
    (CCKW.chainFillingBound_cosetComplex hfill hfold hcount hsum)

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.GHBHyperbolicStokes.faceDegree_outer_eq
#audit_axioms GroupApproximation.GHBHyperbolicStokes.chainFillingBound_of_leastDiscs
#audit_axioms GroupApproximation.KMSGroup.CCKW.chainFillingBound_cosetComplex
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.isHyperbolicGroup_ghb7_of_discInputs
