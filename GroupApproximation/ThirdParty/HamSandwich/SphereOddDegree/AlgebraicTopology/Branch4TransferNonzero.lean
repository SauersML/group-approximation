import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferTopClass
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureConstruction
import Mathlib

/-!
# Branch 4 — Transfer nonzero from the cell model (Prompt 54)

This file packages the Prompt-53 top-class computation (in
`Branch4TransferTopClass.lean`) together with Branch 3's top-cohomology
computation into the project's nonzero-transfer predicate

```text
RPToSphereTransferTopNonzero n
  := ∀ c : sphereCohomology n n, c ≠ 0 → (cohTransferZMod2 n n).hom c ≠ 0
```

recorded in `CoveringTransferHomology.lean`.

## Contents

* `b4_rpTopClass_ne_zero_from_branch3` — the RPⁿ top cohomology class `αⁿ` is
  nonzero, from Branch 3's `rpAlpha_power_topClass`.
* `b4_sphereTopClass_ne_zero` — the chosen sphere top cohomology class `u_S`
  bundled in `B4TopData` is nonzero (its Kronecker pairing with `s_n` is `1`).
* `b4_RPToSphereTransferTopNonzero` — the full top-degree nonzero preservation of
  the cohomology transfer.

## Why the sphere-side rank-one input is needed

The Prompt-53 theorem `b4_cohTransfer_sphereTopClass_ne_zero` shows the transfer
is nonzero on the *specific* class `u_S = d.sphereTopClass`. The project predicate
`RPToSphereTransferTopNonzero n` asks for nonvanishing on *every* nonzero top
sphere class `c`. Over `F₂` this is exactly the same statement once the top
sphere cohomology group `Hⁿ(Sⁿ; F₂)` is one-dimensional: then every nonzero `c`
equals the fixed nonzero `u_S` (`eq_of_finrank_one_of_ne_zero`), and the result
reduces to the Prompt-53 fact. Following the project's practice of bundling honest
missing algebraic-topology inputs as hypotheses, the one-dimensionality of
`Hⁿ(Sⁿ; F₂)` is taken as the hypothesis `hsphere`.

No `axiom`, `sorry`, or placeholder is used; the transfer is the genuine wrong-way
map `cohTransferZMod2` (`b4_cohTransferSphereToRP`).
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **RPⁿ top class nonzero (from Branch 3).** The actual top cohomology class
`αⁿ = b4_rpTopClass n I.monodromy ∈ Hⁿ(RPⁿ; F₂)` is nonzero, given the Branch-3
multiplicative identification `I : RPnGeneratorIdentification n`. This is a thin
restatement of `rpAlpha_power_topClass`. -/
theorem b4_rpTopClass_ne_zero_from_branch3 (n : ℕ) (I : RPnGeneratorIdentification n) :
    b4_rpTopClass n I.monodromy ≠ 0 :=
  rpAlpha_power_topClass I

/-- The chosen sphere top cohomology class `u_S = d.sphereTopClass` is nonzero:
its Kronecker pairing with `s_n` is `1`, so it cannot be the zero class. -/
theorem b4_sphereTopClass_ne_zero (n : ℕ) (d : B4TopData n) :
    d.sphereTopClass ≠ 0 := by
  intro h
  have hp := d.sphere_pairing
  rw [h] at hp
  simp [b4_pairingSphere] at hp

/-- **Prompt 54 main target: top-degree nonzero preservation.** Given the
Prompt-53 top data `d : B4TopData n` and one-dimensionality of `Hⁿ(Sⁿ; F₂)`
(`hsphere`), the mod-2 cohomology transfer `tr^! : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)` of
the double cover is nonzero on every nonzero top sphere class, i.e. the project
predicate `RPToSphereTransferTopNonzero n` holds. -/
theorem b4_RPToSphereTransferTopNonzero (n : ℕ) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPToSphereTransferTopNonzero n := by
  intro c hc
  have hc_eq : c = d.sphereTopClass :=
    eq_of_finrank_one_of_ne_zero hsphere hc (b4_sphereTopClass_ne_zero n d)
  rw [hc_eq]
  exact b4_cohTransfer_sphereTopClass_ne_zero n d

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

