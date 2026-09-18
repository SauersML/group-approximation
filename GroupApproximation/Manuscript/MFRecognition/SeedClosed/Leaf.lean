import GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:seed` with the bridge and Kotowski--Ollivier inputs closed

Lane gl-assembly-10.  `mf_recognition_complexity.tex`, `\begin{lemma}[the seed]\label{lem:seed}`
(census row c6172bdc109a, census line 655; the lemma sits at tex line 667 of the current file):

> There is a fixed finite presentation $P_-$ whose group $E=G_{P_-}$ is not MF.
>
> *Proof.* Theorem~C of~\cite{NonMF} gives a finitely presented torsion-free group with no
> nontrivial homomorphism to an MF group; such a group is not MF unless it is trivial, and it is
> not.  Fix one finite presentation code $P_-$ for this group.

## Route

`SeedFromTheoremC.not_isOperatorMF_seedCodeC` follows the printed proof over Theorem C's three
least-area inputs `hgreendlinger`, `hbridge`, `hKO`.  Two of them are closed on disk:

* `hbridge := HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`, of type
  `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}` (the universe
  `.{0, 0, 0}` is the one `SeedFromTheoremC` fixes);
* `hKO := KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`, of type
  `Manuscript.NonMF.TheoremC.KotowskiOllivierStatement`.

The closed Greendlinger leaf `GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
(lane gl-assembly-04) is not on disk at authoring time.  Its type is the existing
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (Osin's Lemma 4.4 at
least-area diagrams; true), so the printed-proof endpoint is stated as the `_of_greendlinger`
reduction `manuscriptSentence_seedNotMF_of_greendlinger`.  Once gl-assembly-04 lands, the lane's
target `manuscriptSentence_seedNotMF` is that theorem applied to
`AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0, 0, 0}`: the term
`SeedFromTheoremC.seedCodeC AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}
HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` is the lane's code, definitionally.

This reduction is strictly smaller in proof content than the lane target (the target minus the
leaf) and true (its hypothesis is Osin's Lemma 4.4), and it is not an equivalent restatement of
`SeedRemarkTheoremC`: the bridge and Kotowski--Ollivier binders are gone.

The statement of the lemma itself, "there is a fixed finite presentation whose group is not MF",
is proved unconditionally in `manuscriptSentence_seedExists`, from the closed negative code
`PresentationCodes.negativeCode` (`not_isOperatorMF_negativeCode`, the `\leanverified` badge of
the lemma).  That route does not pass through Theorem C, so the printed *proof* sentence
(row c6172bdc109a) stays partial until the leaf is closed.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace SeedClosed

open PresentationCodes

/-- **`lem:seed`, printed proof, over the Greendlinger leaf only** (tex 667-676): the group of
Theorem C, read from its least-area inputs with the embedded Lemma 5.1 bridge and the
Kotowski--Ollivier input closed, is presented by `seedCodeC` and is not MF. -/
theorem manuscriptSentence_seedNotMF_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ¬ IsOperatorMF (Carrier (SeedFromTheoremC.seedCodeC hgreendlinger
      HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
      KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed)) :=
  SeedFromTheoremC.not_isOperatorMF_seedCodeC hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
    KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed

/-- **`lem:seed` as an existence statement, printed proof, over the Greendlinger leaf only**:
some finite presentation code presents a non-MF group, namely `seedCodeC`. -/
theorem manuscriptSentence_seedExists_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∃ c : PresentationCode, ¬ IsOperatorMF (Carrier c) :=
  ⟨SeedFromTheoremC.seedCodeC hgreendlinger
      HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
      KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed,
    manuscriptSentence_seedNotMF_of_greendlinger hgreendlinger⟩

/-- **`lem:seed`, the statement, unconditionally** (tex 667-669): there is a fixed finite
presentation code `P₋` whose group is not MF.  The code is the closed negative code; every coded
group is finitely presented (`PresentationCodes.Carrier` is a `PresentedGroup` on a `Fin`
alphabet with a `Finset` of relators). -/
theorem manuscriptSentence_seedExists :
    ∃ c : PresentationCode, ¬ IsOperatorMF (Carrier c) :=
  ⟨negativeCode, not_isOperatorMF_negativeCode⟩

/-- **`lem:seed`, the statement with finite presentability spelled out, unconditionally.** -/
theorem manuscriptSentence_seedExistsFinitelyPresented :
    ∃ c : PresentationCode,
      Group.IsFinitelyPresented (Carrier c) ∧ ¬ IsOperatorMF (Carrier c) :=
  ⟨negativeCode, inferInstance, not_isOperatorMF_negativeCode⟩

end SeedClosed
end MFRecognition
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedNotMF_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedExists_of_greendlinger
#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedExists
#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.SeedClosed.manuscriptSentence_seedExistsFinitelyPresented
