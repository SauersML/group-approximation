import GroupApproximation.Kazhdan.GHBSharpExistenceSystolic
import GroupApproximation.GGT.SystolicInvariantClique
import GroupApproximation.Meta.AxiomGuard

/-!
# The fixed-clique theorem for systolic complexes, over the zip move and the mirror fold

`Systolic.exists_invariantClique_of_linksSixLarge` proves the fixed-clique theorem for a triangle
complex `X` over two statements about triangulated discs in `X`: the zip move `hzip` and the mirror
fold `hfold`.  Simple connectivity, 6-large links, local finiteness and the action are the
hypotheses of `CCKW.SystolicInvariantCliqueStatement`, and triangle preservation is not used.

* `CCKW.systolicInvariantClique_of_zipFold`: `SystolicInvariantCliqueStatement`, over the zip
  move and the mirror fold in every triangle complex.
* `CCKW.invariantCliques_of_zipFold`, `CCKW.cckwFiniteOrderConjugateIntoVertex_of_zipFold`,
  `sharpExistence_ghb7_of_zipFoldHyp`: the coset complex of `GHB(7)` needs the two statements only
  in the coset complex, the same leaves as `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold`.  So
  `hT6` drops out of the Kotowski--Ollivier route.

## Manuscript status

Scaffold over the zip move and the mirror fold, lanes kh-torsion and fff-periodic.
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- **The fixed-clique theorem for systolic triangle complexes**, over the zip move and the
mirror fold of triangulated discs in every triangle complex. -/
theorem systolicInvariantClique_of_zipFold
    (hzip : ∀ (V : Type) (X : Systolic.TriangleComplex V), Systolic.ZipSpurStatement X)
    (hfold : ∀ (V : Type) (X : Systolic.TriangleComplex V), Systolic.MirrorFoldStatement X) :
    SystolicInvariantCliqueStatement := by
  intro V X Γ _ _ ρ hsc hconn h6 hfin _
  exact Systolic.exists_invariantClique_of_linksSixLarge (hzip V X) (hfold V X) hsc hconn h6 hfin
    ρ

/-- **Every element of finite order of `GHB(7)` maps a nonempty clique of the coset complex into
itself**, over the zip move and the mirror fold in the coset complex. -/
theorem invariantCliques_of_zipFold (hzip : Systolic.ZipSpurStatement cosetComplex)
    (hfold : Systolic.MirrorFoldStatement cosetComplex)
    (hsc : Systolic.SimplyConnected cosetComplex) (hconn : cosetComplex.G.Connected)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    ∀ g : GHB 7, IsOfFinOrder g → ∃ σ : Finset Vertex, σ.Nonempty ∧
      cosetComplex.G.IsClique (σ : Set Vertex) ∧ ∀ x ∈ σ, cosetAction g x ∈ σ := by
  intro g hg
  haveI : Finite (Subgroup.zpowers g) := hg.finite_zpowers.to_subtype
  obtain ⟨σ, hne, hcl, hinv⟩ := Systolic.exists_invariantClique_of_linksSixLarge hzip hfold hsc
    hconn (cosetComplex_linksSixLarge h3 h4) cosetComplex_locallyFinite
    (cosetAction.comp (Subgroup.zpowers g).subtype)
  exact ⟨σ, hne, hcl, fun x hx => hinv ⟨g, Subgroup.mem_zpowers g⟩ x hx⟩

/-- **CCKW Theorem 3.1(ii), cyclic case, for `GHB(7)`**, over the zip move and the mirror fold in
the coset complex. -/
theorem cckwFiniteOrderConjugateIntoVertex_of_zipFold
    (hzip : Systolic.ZipSpurStatement cosetComplex)
    (hfold : Systolic.MirrorFoldStatement cosetComplex) : CCKWFiniteOrderConjugateIntoVertex :=
  cckwFiniteOrderConjugateIntoVertex_of_invariantCliques
    (invariantCliques_of_zipFold hzip hfold CCKWTits.cckwCosetComplex_simplyConnected
      CCKWTits.cckwCosetComplex_connected card_U3_seven_le card_U4_seven_le)

end CCKW

/-- **`SharpExistence` from `GHB(7)`**, over the zip move and the mirror fold in the coset
complex, and hyperbolicity. -/
theorem sharpExistence_ghb7_of_zipFoldHyp (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex)
    (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) : Hyperbolic.SharpExistence :=
  GHBQuotient.sharpExistence_of_ghb7ConjHyp
    (CCKW.cckwFiniteOrderConjugateIntoVertex_of_zipFold hzip hfold) hhyp

end KMSGroup
end GroupApproximation

open GroupApproximation.KMSGroup

#audit_axioms CCKW.systolicInvariantClique_of_zipFold
#audit_axioms CCKW.invariantCliques_of_zipFold
#audit_axioms CCKW.cckwFiniteOrderConjugateIntoVertex_of_zipFold
#audit_axioms sharpExistence_ghb7_of_zipFoldHyp
