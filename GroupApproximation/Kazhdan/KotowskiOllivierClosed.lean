import GroupApproximation.Kazhdan.GHBHyperbolicDiscCounts
import GroupApproximation.Kazhdan.GHBSharpExistenceSystolic
import GroupApproximation.Kazhdan.CCKWSystolicInvariantClique
import GroupApproximation.GGT.SystolicDiscZip
import GroupApproximation.GGT.SystolicDiscMirrorFoldDistinct
import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kotowski--Ollivier input of the Fournier-Facio paragraph, from `GHB(7)`

`TheoremC.KotowskiOllivierStatement` is `Hyperbolic.SharpExistence`: an infinite, finitely
presented, torsion-free hyperbolic group with property (T).  It is the binder `hKO` of every
endpoint of `Manuscript/NonMF/TorsionFreeLiteratureInputsLeastArea.lean`, and the open `sorry`
`TheoremC.kotowskiOllivier` of `Manuscript/NonMF/TheoremCAssembly.lean`.  It carries the start of
the paragraph at tex line 1675 (`\S\ref{sec:torsion-free}`):

> Fournier-Facio constructs a finitely presented torsion-free group $G_0$ with
> property~\textup{(T)}, a subgroup $\Gamma\le G_0$ with property~\textup{(T)}, an element
> $t\in G_0$ with $t\Gamma t^{-1}\le\Gamma$, and a subgroup $J\le G_0$ isomorphic to a finitely
> presented infinite simple group, such that $[\Gamma,J]=1$ and $tJt^{-1}\le\Gamma$~\cite[\S2]{FFF}.

The witness is the Kac--Moody--Steinberg group `GHB(7)`.  Property (T) is `hasKazhdanPropertyT_ghb7`
(`Kazhdan/EJZAngleGHB`), the orders of `U₃(7)`, `U₄(7)` are `card_U3_seven_le`, `card_U4_seven_le`,
Tits' lemma is `CCKWTits.cckwCosetComplex_simplyConnected`, and the typed count and the boundary
sums are `CCKW.typedCountStatement_cosetComplex` and `GHBHyperbolicStokes.boundarySumStatement`.

* `kotowskiOllivier_of_leaves` composes `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` with
  `sharpExistence_ghb7_of_fixedCliqueHyp`, over the zip move `hzip`, the mirror fold `hfold` and
  the fixed-clique theorem `hT6`.
* `kotowskiOllivier_of_pinched` closes the zip move (`CCKW.zipSpur_cosetComplex`) and the
  distinct case of the mirror fold (`Systolic.mirrorFoldDistinct`), and uses
  `sharpExistence_ghb7_of_zipFoldHyp`, which needs no `hT6`.  One leaf stays open:
  `hpinch : Systolic.MirrorFoldPinchedStatement CCKW.cosetComplex`, HC6 at a common third vertex
  (lane fff-periodic).

## Manuscript status

Scaffold over the pinched mirror fold.  The closed `kotowskiOllivier_closed` is one application of
`kotowskiOllivier_of_pinched` once it lands.
-/

namespace GroupApproximation
namespace KMSGroup
namespace KotowskiOllivierClosed

/-- **The hyperbolic property (T) input of [FFF §2], from `GHB(7)`** (tex line 1675), over the
zip move and the mirror fold of triangulated discs in the coset complex, and the fixed-clique
theorem for systolic complexes. -/
theorem kotowskiOllivier_of_leaves (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex)
    (hT6 : CCKW.SystolicInvariantCliqueStatement) :
    Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
  sharpExistence_ghb7_of_fixedCliqueHyp hT6
    (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold)

/-- **The hyperbolic property (T) input of [FFF §2], from `GHB(7)`** (tex line 1675), over the
mirror fold of triangulated discs in the coset complex at a common third vertex. -/
theorem kotowskiOllivier_of_pinched
    (hpinch : Systolic.MirrorFoldPinchedStatement CCKW.cosetComplex) :
    Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
  have hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex :=
    Systolic.mirrorFoldStatement_of_cases (Systolic.mirrorFoldDistinct CCKW.cosetComplex) hpinch
  sharpExistence_ghb7_of_zipFoldHyp CCKW.zipSpur_cosetComplex hfold
    (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold CCKW.zipSpur_cosetComplex hfold)

end KotowskiOllivierClosed
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_leaves
#audit_axioms GroupApproximation.KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_pinched
