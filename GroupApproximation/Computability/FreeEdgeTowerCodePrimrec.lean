import GroupApproximation.Computability.FreeEdgeTowerCode

/-!
# Primitive recursion for the free-edge tower fold

This small follow-on module contains the one elaboration-heavy fact omitted
from `FreeEdgeTowerCode`: primitive recursiveness of folding `edgeCode` over
the finite `tau_j` family.  The raw syntax and its marked semantic obligations
remain available without elaborating this fold.
-/

namespace GroupApproximation
namespace FreeEdgeTowerCode

open PresentationCodes RawTransform CoprodCode
open GroupApproximation.RawWord
open RawTransformPrimrec

set_option maxHeartbeats 800000 in
/-- Iterating the one-edge code constructor over a finite family is primitive
recursive. -/
theorem primrec_multiEdgeCode :
    Primrec₂ (fun (c : PresentationCode)
      (layers : List (List (Raw × Raw))) => multiEdgeCode c layers) := by
  change Primrec (fun a : PresentationCode × List (List (Raw × Raw)) =>
    multiEdgeCode a.1 a.2)
  have hedgeCode : Primrec
      (fun a : PresentationCode × List (Raw × Raw) => edgeCode a.1 a.2) :=
    primrec_edgeCode
  have hstep : Primrec₂
      (fun (z : (PresentationCode × List (List (Raw × Raw))) × PresentationCode)
        (edges : List (Raw × Raw)) => edgeCode z.2 edges) := by
    exact (hedgeCode.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  exact Primrec.list_foldl Primrec.snd Primrec.fst hstep

/-- The whole `tau_j`, `d`, `sigma`, detector-last compiler is primitive
recursive. -/
theorem primrec_compile : Primrec compile := by
  have hedgeCode : Primrec
      (fun a : PresentationCode × List (Raw × Raw) => edgeCode a.1 a.2) :=
    primrec_edgeCode
  have hmultiEdgeCode : Primrec
      (fun a : PresentationCode × List (List (Raw × Raw)) =>
        multiEdgeCode a.1 a.2) := primrec_multiEdgeCode
  have hTau : Primrec (fun x : TowerInput => multiEdgeCode x.1 x.2.1) :=
    hmultiEdgeCode.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hD : Primrec (fun x : TowerInput =>
      edgeCode (multiEdgeCode x.1 x.2.1) x.2.2.1) :=
    hedgeCode.comp
      (Primrec.pair hTau
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hSigma : Primrec (fun x : TowerInput =>
      threeStageCode x.1 x.2.1 x.2.2.1 x.2.2.2.1) :=
    hedgeCode.comp
      (Primrec.pair hD
        (Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hDetector : Primrec (fun x : TowerInput =>
      centralEdges x.2.2.2.2) :=
    primrec_centralEdges.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact hedgeCode.comp (Primrec.pair hSigma hDetector)

theorem computable_compile : Computable compile := primrec_compile.to_comp

end FreeEdgeTowerCode
end GroupApproximation
