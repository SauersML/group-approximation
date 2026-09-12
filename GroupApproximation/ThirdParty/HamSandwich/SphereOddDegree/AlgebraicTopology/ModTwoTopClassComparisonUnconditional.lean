import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoTopDegreeAction
import Mathlib

/-!
# Prompt 06 — Assemble `ModTwoTopClassComparison` unconditionally

This file exposes the public Branch-2 comparison theorem
`modTwoTopClassComparison_unconditional`, eliminating the final Branch-2
hypothesis `hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)`.

It is a thin wrapper over the outputs of Prompts 04 and 05, namely
`construct_SphereModTwoTopData` and the existing theorem
`modTwoTopClassComparison_of_data`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Branch 2 closed: the mod-two top-class comparison for the unconditional
sphere top-homology identification. -/
theorem modTwoTopClassComparison_unconditional
    (n : ℕ) (hn : 1 ≤ n) :
    ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn) :=
  modTwoTopClassComparison_of_data
    (sphereTopHomologyIso_unconditional n hn)
    (construct_SphereModTwoTopData n hn)

/-- Same theorem in the exact form used by the final theorem. -/
theorem final_modTwoTopClassComparison
    {n : ℕ} (hn : 1 ≤ n) :
    ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn) :=
  modTwoTopClassComparison_unconditional n hn

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

