import GroupApproximation.Manuscript.MFRecognition.SeedPresentation
import GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC

/-!
# `lem:seed` as printed: the Theorem C seed

`SeedPresentation` runs the FIN/INF switch on the repository's closed
negative presentation code, which is non-MF with no hypothesis.  The printed
proof of `lem:seed` takes its seed from Theorem C instead.  This module
records that reading, and it is the only place where the two meet.

The seeds are interchangeable: `lem:switch` and both branch lemmas use only
that the seed is finitely presented and not MF, and neither reads the code
itself.  Keeping the printed reading here rather than in `SeedPresentation`
keeps `Manuscript.NonMF.TheoremCAssembly` out of the import closure of the
recognition chain, so that chain carries none of Theorem C's three hypotheses
(`hgreendlinger`, `hbridge`, `hKO`; see `SeedFromTheoremC`).
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Switch

open PresentationCodes

/-- **`lem:seed` as printed**: the group of Theorem C is a finitely presented
non-MF seed as well, over Theorem C's three least-area hypotheses.
Interchangeable with `seedCode`, which carries no hypothesis. -/
theorem seedCodeC_not_isOperatorMF
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : NonMF.TheoremC.KotowskiOllivierStatement) :
    ¬ IsOperatorMF (Carrier (SeedFromTheoremC.seedCodeC hgreendlinger hbridge hKO)) :=
  SeedFromTheoremC.not_isOperatorMF_seedCodeC hgreendlinger hbridge hKO

end Switch
end MFRecognition
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.MFRecognition.Switch.seedCodeC_not_isOperatorMF
