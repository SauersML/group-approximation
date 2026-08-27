import GroupApproximation.Computability.FreeEdgeTowerCode

/-!
# Primitive recursion for the free-edge tower fold

This small follow-on module contains the one elaboration-heavy fact omitted
from `FreeEdgeTowerCode`: primitive recursiveness of folding `edgeCode` over
the finite `tau_j` family.  The raw syntax and its marked semantic obligations
remain available without elaborating this fold.

## Why the fold is proved at abstract carriers

`Primrec.list_foldl` is `list_foldl' (Primcodable.prim _)`, so every use site
projects `Primcodable.prim` out of the instance for its *element* type, and
its step hypothesis lives at `Primcodable (α × (σ × β))`.  Applied directly at
the concrete alphabet that is a four-deep encoding tower --- the ambient
`PresentationCode × List (List (Raw × Raw))` paired with
`PresentationCode × List (Raw × Raw)`, each leaf a `List (ℕ × Bool)` --- and
whnf-ing it is where the elaboration went.  `primrec_compile` below, whose
`TowerInput` nests deeper still, never pays this, because it only ever
*composes* already-proved `Primrec` facts.

So the fold is proved once in `primrec_foldl`, at abstract carriers where
every `Primcodable` argument is a variable and no encoding can be unfolded.
The concrete statement is then a substitution into that finished proof, which
the elaborator never has to reduce.
-/

namespace GroupApproximation
namespace FreeEdgeTowerCode

open PresentationCodes RawTransform CoprodCode
open GroupApproximation.RawWord
open RawTransformPrimrec

/-- Folding a primitive recursive binary operation over a list is primitive
recursive.

Stated at abstract carriers deliberately.  Elaborated here, the `Primcodable`
arguments of `Primrec.list_foldl` are variables, so neither its
`Primcodable.prim` projection nor its step hypothesis can unfold an encoding;
the concrete instance below is a substitution into the finished term. -/
theorem primrec_foldl {α β : Type} [Primcodable α] [Primcodable β]
    {op : α → β → α} (hop : Primrec (fun z : α × β => op z.1 z.2)) :
    Primrec (fun p : α × List β => p.2.foldl op p.1) := by
  have hstep : Primrec₂
      (fun (_ : α × List β) (q : α × β) => op q.1 q.2) :=
    (hop.comp Primrec.snd).to₂
  exact Primrec.list_foldl Primrec.snd Primrec.fst hstep

/-- Iterating the one-edge code constructor over a finite family is primitive
recursive.  `multiEdgeCode c layers` is `layers.foldl edgeCode c` by
definition, so this is `primrec_foldl` at `op := edgeCode`. -/
theorem primrec_multiEdgeCode :
    Primrec₂ (fun (c : PresentationCode)
      (layers : List (List (Raw × Raw))) => multiEdgeCode c layers) :=
  primrec_foldl (op := edgeCode) primrec_edgeCode

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
