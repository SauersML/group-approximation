import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNoCup
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremBranch2Discharged
import Mathlib

/-!
# Prompt 01 — Direct final path via the actual class `actualRPAlpha n`

This file realises the "shorter direct route" of Prompt 01: it builds
`OddMapFixesTopClass n`, and hence the near-final odd-degree theorem, **without**
passing through the strict `RPnCellularCochainStructure n` or even the full
`RPnGeneratorIdentification n` interface.

The preferred path uses only:

* `actualRPAlpha n` — the canonical degree-one class in `H¹(RPⁿ; F₂)`;
* `actualRPAlpha_topPower_ne_zero_no_cup` — unconditional Gysin-route
  nonvanishing of its top cup power;
* `inducedOnRPPullback_actualRPAlpha` — descended odd maps fix `actualRPAlpha n`;
* `inducedOnRP_cohPullback_cupPow_fixed` — cup-power naturality, lifting
  fixedness from `α` to `αⁿ`;
* `RPnTopClassTransfer n` — the remaining honest double-cover transfer predicate;
* `odd_degree_of_odd_sphere_self_map_branch2_discharged` — Branch 2 discharged.

No `axiom`, `constant`, `opaque`, `unsafe`, `sorry`, or `admit` is used.  The old
cellular-based routes stay in place as compatibility wrappers; they are no longer
on this preferred final path.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Descended odd maps fix the top cup power of the actual class
`actualRPAlpha n`, without any cellular-cochain structure. -/
theorem actualRPAlpha_topPower_fixed_no_cellular {n : ℕ}
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    inducedOnRPPullback f hf n (cupPowZMod2 (actualRPAlpha n) n)
      = cupPowZMod2 (actualRPAlpha n) n := by
  have hfix1 :
      (cohPullback (TopCat.ofHom (inducedOnRP f hf)) 1).hom (actualRPAlpha n)
        = actualRPAlpha n := by
    convert inducedOnRPPullback_actualRPAlpha (n := n) f hf using 1 <;> rfl
  convert inducedOnRP_cohPullback_cupPow_fixed f hf (actualRPAlpha n) hfix1 n using 1 <;> rfl

/-- Minimal actual-top-power datum.  This is the concrete version of the
`RPnActualTopPowerData` interface suggested by Prompt 01.  It depends only on the
actual class `actualRPAlpha n`, not on any cellular-cochain structure. -/
structure RPnActualTopPowerData (n : ℕ) where
  topPower_ne_zero : cupPowZMod2 (actualRPAlpha n) n ≠ 0
  topPower_fixed : ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f),
    inducedOnRPPullback f hf n (cupPowZMod2 (actualRPAlpha n) n)
      = cupPowZMod2 (actualRPAlpha n) n

/-- Construct the minimal top-power datum from the already-established no-cup
Gysin nonvanishing theorem and cup-power naturality. -/
theorem construct_RPnActualTopPowerData (n : ℕ) (hn : 1 ≤ n) :
    RPnActualTopPowerData n where
  topPower_ne_zero := actualRPAlpha_topPower_ne_zero_no_cup n hn
  topPower_fixed := fun f hf => actualRPAlpha_topPower_fixed_no_cellular f hf

/-- `OddMapFixesTopClass n` follows from the actual top power and the remaining
honest transfer predicate.  This removes both `RPnCellularCochainStructure n` and
`RPnGeneratorIdentification n` from the preferred final path. -/
theorem oddMapFixesTopClass_of_actualTopPower_and_transfer {n : ℕ}
    (hn : 1 ≤ n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n := by
  intro f hf
  exact htr f hf (cupPowZMod2 (actualRPAlpha n) n)
    (actualRPAlpha_topPower_fixed_no_cellular f hf)
    (actualRPAlpha_topPower_ne_zero_no_cup n hn)

/-- Same assembly, packaged from the minimal datum `RPnActualTopPowerData n`. -/
theorem oddMapFixesTopClass_of_actualTopPowerData {n : ℕ}
    (T : RPnActualTopPowerData n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n := by
  intro f hf
  exact htr f hf (cupPowZMod2 (actualRPAlpha n) n)
    (T.topPower_fixed f hf) T.topPower_ne_zero

/-- **Preferred near-final theorem (Prompt 01).**  Branch 2 is discharged, so the
odd-degree conclusion needs only `1 ≤ n` and the remaining honest transfer
predicate `RPnTopClassTransfer n`.  There is no `RPnCellularCochainStructure n`
and no `RPnGeneratorIdentification n` input on this path. -/
theorem odd_degree_of_odd_sphere_self_map_from_transfer {n : ℕ}
    (hn : 1 ≤ n) (htr : RPnTopClassTransfer n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_branch2_discharged hn
    (oddMapFixesTopClass_of_actualTopPower_and_transfer hn htr) f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
