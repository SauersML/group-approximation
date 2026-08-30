import Palomar.Solution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel audit of the Palomar result

The source scan rejects admissions and escape hatches in every Lean file. This
driver checks the complementary kernel-level facts: the theorem has the exact
advertised statement, its proof uses only Lean's standard classical axioms,
and no declaration in the surviving proof library depends on anything else.
-/

open Lean Elab Command

namespace GroupApproximation.Audit

example :
    ExplicitNonMF.IsSoficGroup ExplicitNonMF.E ∧
      ¬ ExplicitNonMF.IsSequentialOperatorMFGroup ExplicitNonMF.E :=
  ExplicitNonMF.explicit_sofic_not_MF

/-- The classical axioms used by Mathlib and permitted by the comparator. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- All declarations whose names begin with one of the supplied namespaces. -/
def projectDeclarations (env : Environment) (roots : List Name) : Array Name :=
  env.constants.fold (init := #[]) fun declarations name _ ↦
    if roots.any (·.isPrefixOf name) then declarations.push name else declarations

/-- The union of the transitive axiom closures of the supplied declarations. -/
def axiomClosure (roots : Array Name) : CommandElabM (Array Name) := do
  let mut result := #[]
  for name in roots do
    for ax in (← collectAxioms name) do
      unless result.contains ax do
        result := result.push ax
  return result

def disallowed (axioms : Array Name) : Array Name :=
  axioms.filter fun ax ↦ !allowedAxioms.contains ax

run_cmd do
  let env ← getEnv
  let headline := ``ExplicitNonMF.explicit_sofic_not_MF
  let headlineAxioms ← collectAxioms headline
  let headlineBad := disallowed headlineAxioms
  unless headlineBad.isEmpty do
    throwError "the Palomar theorem depends on disallowed axioms: {headlineBad.toList}"
  logInfo m!"{headline} depends on: {headlineAxioms.toList}"

  let declarations := projectDeclarations env [`GroupApproximation, `ExplicitNonMF]
  if declarations.size < 100 then
    throwError "only {declarations.size} project declarations found; the audit is not seeing the library"
  let axioms ← axiomClosure declarations
  let bad := disallowed axioms
  unless bad.isEmpty do
    throwError "the surviving proof library depends on disallowed axioms: {bad.toList}"
  logInfo m!"audited {declarations.size} declarations; no disallowed axioms"

end GroupApproximation.Audit
