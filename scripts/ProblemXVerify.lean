import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Independent verification driver for STW Problem X(1)

`lake env lean scripts/ProblemXVerify.lean` (via `scripts/remote-build.sh
--run scripts/ProblemXVerify.lean`).

`#audit_closed_axioms` inside `Manuscript/NinetyNineProblems/ProblemX.lean`
already gates two things at the endpoint: that the elaborated type has no
leading binder, and that the transitive axiom closure is
`propext / Classical.choice / Quot.sound`.  It does **not** run the third
check `scripts/Audit.lean` runs, the literature quarantine --- the walk over
the *statement's* constant closure looking for a package this repository does
not prove.  That walk is seeded at `headlineTheorems ++ zeroInputEndpoints`,
and no `NinetyNineProblems` name is on either roster, so nothing in the
corpus currently asks whether `not_problemX1Statement` states a citation.

This driver asks.  It re-runs the quarantine walk at the Problem X(1)
endpoints, with the roster of `scripts/Audit.lean` copied by name, and it
prints the whole `GroupApproximation`-namespace part of each statement
closure so a reader can check the list rather than trust the filter.  It also
re-prints the axiom closures, because the build log only carries the tail.

Read-only: it defines nothing the corpus imports and writes no file.
-/

open Lean Elab Command

namespace ProblemXVerify

/-- `literaturePackages` of `scripts/Audit.lean`, by fully qualified name.
A name absent from this environment is reported and skipped: the walk below
runs in the import closure of `ProblemX`, and a package outside that closure
cannot appear in a statement inside it. -/
def roster : List Name :=
  [`GroupApproximation.QuasidiagonalMF.TikuisisWhiteWinterInput,
   `GroupApproximation.QuasidiagonalMF.AmenableNuclearInput,
   `GroupApproximation.QuasidiagonalMF.AmenableUCTInput,
   `GroupApproximation.QuasidiagonalMF.AmenableMFInput,
   `GroupApproximation.CyclicBaseCalibration.AmenableImpliesMF,
   `GroupApproximation.FournierFacioUniversal.UniversalTorsionFreeHost,
   `GroupApproximation.ChiodoHost.TorsionFreeHigmanHull,
   `GroupApproximation.Higman.OperationClosures,
   `GroupApproximation.Higman.HigmanTheoremThree,
   `GroupApproximation.Higman.TransportSectionFive,
   `GroupApproximation.Higman.REBenignTF,
   `GroupApproximation.Higman.REBenign,
   `GroupApproximation.Higman.CountableToFG,
   `GroupApproximation.Higman.BridgeRecursive,
   `GroupApproximation.Higman.TorsionPreservation,
   `GroupApproximation.Higman.TorsionFreeHigmanEmbedding,
   `GroupApproximation.Higman.AbsorberRecursivePresentation,
   `GroupApproximation.FournierFacioUniversal.KazhdanEnvelope,
   `GroupApproximation.SmallCancellationEnvelope.HyperbolicKazhdanPartner,
   `GroupApproximation.FournierFacioUniversal.UniversalKazhdanGroup,
   `GroupApproximation.ContainsSquareWitness.UniversalFPTorsionFree,
   `GroupApproximation.SmallCancellationRouter.GreendlingerGate,
   `GroupApproximation.SmallCancellationRouter.RoutingLemmaData,
   `GroupApproximation.DefectRoutingData,
   `GroupApproximation.OrderPreservingRoutingData,
   `GroupApproximation.FiveConditionRoutingData,
   `GroupApproximation.RelativeCommonQuotientData,
   `GroupApproximation.FournierFacioDefectData,
   `GroupApproximation.KunThomShulmanDoubleData,
   `GroupApproximation.CStarRecognitionConsequences.GroupCStarAdianRabinReductions]

/-- The endpoints under test. -/
def endpoints : List Name :=
  [`GroupApproximation.NinetyNineProblems.not_problemX1Statement,
   `GroupApproximation.NinetyNineProblems.ProblemX1Statement,
   `GroupApproximation.NinetyNineProblems.literalFactorizationProperty,
   `GroupApproximation.NinetyNineProblems.LiteralFactorizationProperty,
   `GroupApproximation.NinetyNineProblems.literalCanonicalTrace_hyperlinear_not_quasidiagonal,
   `GroupApproximation.NinetyNineProblems.literalCanonicalTrace_isHyperlinearTrace,
   `GroupApproximation.NinetyNineProblems.literalCanonicalTrace_not_isQuasidiagonalTrace,
   `GroupApproximation.NinetyNineProblems.isHyperlinearTrace_of_isAmenableTrace,
   `GroupApproximation.NinetyNineProblems.not_problemX1Statement_of_literalFactorizationProperty,
   `GroupApproximation.NinetyNineProblems.literalCanonicalTrace_isTracialState,
   `GroupApproximation.LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt]

/-- **Non-vacuity calibration.**  `¬ IsQuasidiagonalTrace τ_E` is only a
refutation of Brown's question if `IsQuasidiagonalTrace` can hold at all: a
predicate no trace satisfies would make the negative half free and the
endpoint an artefact of the transcription rather than a theorem about `E`.
The same asymmetry runs the other way for `IsAmenableTrace`, which the
positive half must satisfy at `τ_E` and which therefore must not be so weak
that everything satisfies it --- the first entry below is the one that
separates the two, since it says quasidiagonal implies amenable and nothing
in the corpus proves the converse.

Each name here is printed with its type, so a reader can see that the scalar
witness is a genuine model on `ℂ` and not a degenerate one. -/
def calibration : List Name :=
  [`GroupApproximation.Quasidiagonal.isAmenableTrace_of_isQuasidiagonalTrace,
   `GroupApproximation.Quasidiagonal.isQuasidiagonalTrace_complex,
   `GroupApproximation.Quasidiagonal.isAmenableTrace_complex,
   `GroupApproximation.Quasidiagonal.isCompletelyPositiveOnMatrices_zero,
   `GroupApproximation.Quasidiagonal.ucpContractive,
   `GroupApproximation.Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace]

/-- Every constant reachable from `seeds`, unfolding through the type *and*
the value of everything it meets, and through a structure's constructors --- a
transcription of `reachableFrom` in `scripts/Audit.lean`. -/
partial def reachableFrom (env : Environment) (visited : NameSet) :
    List Name → NameSet
  | [] => visited
  | n :: rest =>
    if visited.contains n then reachableFrom env visited rest
    else
      let visited := visited.insert n
      match env.find? n with
      | some ci =>
          let ctors := match ci with
            | .inductInfo iv => iv.ctors
            | _ => []
          reachableFrom env visited
            (ci.getUsedConstantsAsSet.toList ++ ctors ++ rest)
      | none => reachableFrom env visited rest

/-- The constants of a declaration's **type**: where the quarantine walk
starts, so that a proof term mentioning a package is not a finding. -/
def statementConstants (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.type.getUsedConstants.toList
  | none => []

run_cmd do
  let env ← getEnv

  logInfo "=== roster presence in the ProblemX import closure ==="
  let mut present : List Name := []
  for p in roster do
    if env.contains p then present := present ++ [p]
  logInfo m!"roster entries reachable as names here: {present.length} of \
{roster.length}: {present}"

  for r in endpoints do
    unless env.contains r do
      logError m!"MISSING declaration: {r}"

  logInfo "=== per-endpoint report ==="
  for r in endpoints do
    if let some ci := env.find? r then
      logInfo m!"---- {r}\n  leading binder: {ci.type.isForall}\n  type: {ci.type}"
      let closure := (← collectAxioms r).qsort Name.lt
      logInfo m!"  axioms: {closure.toList}"
      let reach := reachableFrom env {} (statementConstants env r)
      let reachList := reach.toList
      let hits := roster.filter (fun p => reach.contains p)
      logInfo m!"  statement closure size: {reachList.length}"
      logInfo m!"  literature packages named by the STATEMENT: {hits}"
      -- Every corpus-defined constant the statement can reach, so the filter
      -- above can be checked against the list rather than trusted.
      let ours := reachList.filter
        (fun n => Name.isPrefixOf `GroupApproximation n)
      logInfo m!"  corpus constants in the statement closure \
({ours.length}): {(ours.toArray.qsort Name.lt).toList}"

  logInfo "=== non-vacuity calibration ==="
  for r in calibration do
    match env.find? r with
    | none => logError m!"MISSING calibration declaration: {r}"
    | some ci =>
        let closure := (← collectAxioms r).qsort Name.lt
        logInfo m!"---- {r}\n  type: {ci.type}\n  axioms: {closure.toList}"

end ProblemXVerify

/-! ## Name-resolution check for the roster entries added to `scripts/Audit.lean`

The corpus-wide audit needs a fully built `.lake`, which a tree with an
unbuilt module does not have, so a mis-spelled roster entry could sit on main
until the next full build.  These three are spelled exactly as
`zeroInputEndpoints` spells them, inside the namespace that file is in, so a
resolution failure is an error here instead. -/
namespace GroupApproximation.Audit

/-- The `NinetyNineProblems` entries of `zeroInputEndpoints`. -/
def problemXZeroInputEndpoints : List Lean.Name :=
  [``NinetyNineProblems.not_problemX1Statement,
   ``NinetyNineProblems.literalFactorizationProperty,
   ``NinetyNineProblems.literalCanonicalTrace_hyperlinear_not_quasidiagonal]

run_cmd Lean.logInfo m!"audit roster entries resolve: {problemXZeroInputEndpoints}"

end GroupApproximation.Audit
