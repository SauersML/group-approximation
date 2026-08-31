import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferSurjective
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNaturality
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing

/-!
# Assembly of `RPnTopClassTransfer n` (Prompt 09)

This file assembles the genuine mod-2 transfer/Gysin infrastructure of the double
cover `proj n : Sⁿ → RPⁿ` (Prompts 04–08) into the top-class transfer predicate

```text
RPnTopClassTransfer n :=
  ∀ (f : C(Sⁿ, Sⁿ)) (hf : IsOddMap f) (a : Hⁿ(RPⁿ; F₂)),
    fbar^* a = a → a ≠ 0 → ∃ c : Hⁿ(Sⁿ; F₂), c ≠ 0 ∧ f^* c = c
```

of `RPnActualAlphaPowerNonvanishing.lean`.

## The honest witness

The intended witness for the sphere class is the genuine top transfer of Prompt 08

```text
c := (rpToSphereTopTransfer n cc).hom a,
```

where `cc : RPnCellularCochainStructure n` is the project's honest cellular-cochain
input (the cellular-approximation datum, absent from pinned Mathlib, that the whole
RPⁿ-cohomology side of the project already depends on). This is *not* the
degenerate ordinary pullback `projPullback`: `rpToSphereTopTransfer` is a genuine
linear **section** of the surjective genuine cohomology transfer
`cohTransferZMod2 n n : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)`.

* `c ≠ 0` is `rpToSphereTopTransfer_nonzero` (Prompt 08): the section is injective.
* `f^* c = c` is proved here from the naturality square of the transfer (Prompt 06,
  `rpToSphereTransfer_naturality_odd`), the section identity
  `rpToSphereTopTransfer_section`, the hypothesis `fbar^* a = a`, and the
  top-degree **injectivity** of the cohomology transfer
  `RPToSphereTransferTopNonzero n` (Prompt 08).

## Why two honest inputs remain (blocker)

A *fully parameterless* `rpnTopClassTransfer (n : ℕ) : RPnTopClassTransfer n` is
**not** attainable with the pinned Mathlib API. Two genuinely Mathlib-absent
topological facts are required and are carried as explicit inputs:

1. `cc : RPnCellularCochainStructure n` — the RPⁿ cellular-approximation datum. It
   is what makes the cohomology transfer surjective in the top degree
   (`cohTransferZMod2_top_surjective`, via `Hⁿ⁺¹(RPⁿ; F₂) = 0`). The whole project
   already carries this honest input; it cannot be built from `n` alone.

2. `RPToSphereTransferTopNonzero n` — top-degree injectivity of the genuine
   cohomology transfer (Prompt 08's "nonzero preservation"). By
   `RPToSphereTransferTopNonzero_of_witness` it reduces to the single homology-side
   residual `TopHomologyTransferNonzeroWitness n`: that the homology transfer
   carries the `F₂`-fundamental class of `RPⁿ` to that of `Sⁿ`. This is the
   genuine remaining algebraic-topology input (the top-degree iso of the mod-2
   double-cover transfer), still absent from pinned Mathlib.

Both inputs are honest, named pieces of infrastructure (not free `Prop`
assumptions invented here), so this assembly genuinely *reduces* the previously
free `RPnTopClassTransfer n` hypothesis to the project's standing topological data
plus the one remaining homology witness. See
`docs/current/Transfer_RPnTopClassTransfer_Assembly_Result.md`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Assembly of `RPnTopClassTransfer n`.** Given the project's honest cellular
input `cc : RPnCellularCochainStructure n` (yielding surjectivity of the genuine
cohomology transfer) and the top-degree injectivity `RPToSphereTransferTopNonzero n`
of the transfer, the double-cover top-class transfer predicate holds: a nonzero
`RPⁿ` top class fixed by a descended odd map is carried to a nonzero sphere top
class fixed by the map.

The sphere witness is the genuine section `(rpToSphereTopTransfer n cc).hom a` of
Prompt 08 — never the degenerate `projPullback`. -/
theorem rpnTopClassTransfer_of_cellular (n : ℕ)
    (cc : RPnCellularCochainStructure n)
    (hinj : RPToSphereTransferTopNonzero n) :
    RPnTopClassTransfer n := by
  intro f hf a ha_fixed ha_nonzero
  refine ⟨(rpToSphereTopTransfer n cc).hom a,
    rpToSphereTopTransfer_nonzero n cc ha_nonzero, ?_⟩
  set cls := (rpToSphereTopTransfer n cc).hom a with hcls
  -- Naturality of the transfer at degree `n`, evaluated at `cls`.
  have hnat := rpToSphereTransfer_naturality_odd (n := n) (k := n) f hf
  have happ := congrArg
    (fun φ : sphereCohomology n n ⟶ rpCohomology n n => φ.hom cls) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  -- The section identity: the transfer of `cls` is `a`.
  have hsec : (cohTransferZMod2 n n).hom cls = a := rpToSphereTopTransfer_section n cc a
  -- Push `fbar^* a = a` through the square: the transfer of `f^* cls` is again `a`.
  rw [hsec] at happ
  have key : (cohTransferZMod2 n n).hom ((spherePullback f n).hom cls) = a := by
    rw [happ]; exact ha_fixed
  -- Both `f^* cls` and `cls` transfer to `a`; injectivity of the transfer forces them equal.
  by_contra hne
  refine hinj ((spherePullback f n).hom cls - cls) (sub_ne_zero.mpr (fun h => hne h)) ?_
  rw [map_sub, key, hsec, sub_self]

/-- **Assembly from the homology witness.** The single homology-side residual
`TopHomologyTransferNonzeroWitness n` (plus the cellular input `cc`) inhabits
`RPnTopClassTransfer n`, via the reduction `RPToSphereTransferTopNonzero_of_witness`. -/
theorem rpnTopClassTransfer_of_cellular_witness (n : ℕ)
    (cc : RPnCellularCochainStructure n)
    (hw : TopHomologyTransferNonzeroWitness n) :
    RPnTopClassTransfer n :=
  rpnTopClassTransfer_of_cellular n cc (RPToSphereTransferTopNonzero_of_witness n hw)

/-- **Downstream integration.** The final odd-map degree theorem with the free
`htr : RPnTopClassTransfer n` hypothesis discharged by the genuine transfer
assembly: the transfer input is replaced by the project's honest cellular datum
`cc` together with the top-degree injectivity `RPToSphereTransferTopNonzero n`. -/
theorem finalComparison_topPowerInput_transferFromCellular {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (I : RPnGeneratorIdentification n)
    (cc : RPnCellularCochainStructure n) (hinj : RPToSphereTransferTopNonzero n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  finalComparison_topPowerInput e hcmp I (rpnTopClassTransfer_of_cellular n cc hinj) f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

