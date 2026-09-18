import GroupApproximation.Manuscript.NonMF.TorsionFreeAlgebraSentencesClosed
import GroupApproximation.Manuscript.NonMF.TorsionFreeCStar.InParticular
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.ChiodoBelegradekTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# The reduced C⋆-algebra of the torsion-free example

`non_mf_groups_exist.tex`, Introduction (tex lines 303–305), after
`thm:torsion-free`:

> Section `sec:torsion-free` builds `Q` from Fournier-Facio's torsion-free
> property-(T) group and Hull's small cancellation theorem.  Its reduced
> C⋆-algebra is simple, has a unique tracial state and stable rank one, and is
> not MF.

## What is proved here

For **every** group `Q` with the properties `thm:torsion-free` prints that the
C⋆-sentence uses — finitely presented (or just countable), torsion-free,
acylindrically hyperbolic, and every homomorphism from `Q` to an MF group
trivial — the four conclusions hold for `C*_r(Q)`, with no hypothesis standing
for a cited theorem:

* *simple* and *unique tracial state*: Dahmani–Guirardel–Osin, Theorem 2.35,
  proved as `TorsionFreePrinted.dgoTheorem235Printed` (Powers-type averaging
  from the naive free-product property, which is proved for acylindrically
  hyperbolic groups with trivial finite radical);
* *stable rank one*: Gerasimova–Osin, Theorem 1.1, proved as
  `TorsionFreePrinted.gerasimovaOsinTheorem11Printed` (Dykema–de la Harpe
  Theorem 1.4, GO Proposition 2.4, Proposition 4.1, Lemma 4.2);
* both are packaged, at torsion-free `Q`, as
  `TorsionFreePrintedSentences.manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed`;
* *not MF*: `reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra` turns
  `¬ IsCDEOperatorMF Q` into `¬ IsMFAlgebra (C*_r Q)` (the last assertion of
  `prop:mf-residual-calculus`), and `Q` is not MF because it is nontrivial
  (`TorsionFreePrinted.nontrivial_of_acylHyperbolic`) and is a nontrivial
  quotient of itself (`manuscriptSentence_noNontrivialQuotientMF`).

## What is not proved here

The existence of `Q` (`thm:torsion-free`, tex 297) is not produced
unconditionally in the corpus: the construction's small-cancellation step
(Hull, Theorem 7.1) stands over Osin's Greendlinger lemma
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, whose
diagram residuals are open.  Hence the sentence is recorded as `partial`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeCStar

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-- **"Its reduced C⋆-algebra is simple, has a unique tracial state and stable
rank one, and is not MF"**, for a countable torsion-free acylindrically
hyperbolic group all of whose homomorphisms to MF groups are trivial. -/
theorem manuscriptSentence_reducedAlgebraOfCountable
    (Q : Type) [Group Q] [Countable Q] [IsAcylindricallyHyperbolic Q]
    (htf : IsPowerTorsionFree Q)
    (hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1) :
    IsSimpleCStar (ReducedGroupCStar Q) ∧
      HasUniqueTracialState (ReducedGroupCStar Q) ∧
        IsStableRankOne (ReducedGroupCStar Q) ∧
          ¬ IsMFAlgebra (ReducedGroupCStar Q) := by
  obtain ⟨hsimple, huniq, hsr⟩ :=
    TorsionFreePrintedSentences.manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed
      Q htf
  have hnotMF : ¬ IsCDEOperatorMF Q := by
    intro hMF
    haveI : Nontrivial Q := TorsionFreePrinted.nontrivial_of_acylHyperbolic Q
    exact manuscriptSentence_noNontrivialQuotientMF Q hkill Q inferInstance
      (MonoidHom.id Q) Function.surjective_id inferInstance
      ((isCDEOperatorMF_iff_isOperatorMF Q).mp hMF)
  exact ⟨hsimple, huniq, hsr,
    (reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra Q hnotMF).2.2⟩

/-- **"Its reduced C⋆-algebra is simple, has a unique tracial state and stable
rank one, and is not MF"**, at the hypotheses printed in `thm:torsion-free`
that the sentence uses: finitely presented (which gives countability),
torsion-free, acylindrically hyperbolic, every homomorphism to an MF group
trivial. -/
theorem manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF
    (Q : Type) [Group Q] [Group.IsFinitelyPresented Q] [IsAcylindricallyHyperbolic Q]
    (htf : IsPowerTorsionFree Q)
    (hkill : ∀ (M : Type) (_ : Group M), IsOperatorMF M →
      ∀ (f : Q →* M) (x : Q), f x = 1) :
    IsSimpleCStar (ReducedGroupCStar Q) ∧
      HasUniqueTracialState (ReducedGroupCStar Q) ∧
        IsStableRankOne (ReducedGroupCStar Q) ∧
          ¬ IsMFAlgebra (ReducedGroupCStar Q) := by
  haveI : Countable Q := ChiodoBelegradek.countable_of_isFinitelyPresented Q
  exact manuscriptSentence_reducedAlgebraOfCountable Q htf hkill

end TorsionFreeCStar
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeCStar.manuscriptSentence_reducedAlgebraOfCountable
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeCStar.manuscriptSentence_reducedAlgebraSimpleUniqueTraceStableRankNotMF
