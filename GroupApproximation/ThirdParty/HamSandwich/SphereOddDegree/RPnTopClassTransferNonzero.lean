import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferHomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality

/-!
# Top-degree nonzero preservation for the double-cover transfer (Prompt 08)

This file (Prompt 08 of the transfer/Gysin sequence) studies the **top-degree
nonzero preservation** of the genuine mod-2 cohomology transfer
`cohTransferZMod2 n n : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)` of the double cover
`proj n : Sⁿ → RPⁿ` constructed in Prompts 04–06.

## Direction note

As recorded in `CoveringTransferHomology.lean`, the genuine cohomology transfer
goes **cover → base**, `Hⁿ(Sⁿ) ⟶ Hⁿ(RPⁿ)`; it is *not* the degenerate ordinary
pullback `projPullback` (`proj^*`), and no non-degenerate linear map in the
opposite direction `Hⁿ(RPⁿ) ⟶ Hⁿ(Sⁿ)` arises from dualizing a chain map (the
only chain map `C_•(Sⁿ) ⟶ C_•(RPⁿ)` is the pushforward `proj_*`, whose dual is
exactly `projPullback`). The "nonzero preservation" of Prompt 08 is therefore the
predicate `RPToSphereTransferTopNonzero n` of `CoveringTransferHomology.lean`:

```text
∀ c : Hⁿ(Sⁿ; F₂), c ≠ 0 → (cohTransferZMod2 n n) c ≠ 0,
```

i.e. the transfer is injective (hence — both top groups being one-dimensional over
`F₂` — an isomorphism) in the top degree. The Prompt-09 assembly of
`RPnTopClassTransfer n` then produces a fixed nonzero sphere class from a fixed
nonzero `RPⁿ` class by *inverting* this iso, using the naturality square of
Prompt 06 (`rpToSphereTransfer_naturality_odd`).

## What is proved here (genuine, placeholder-free)

The project already contains the degree-`n` **universal coefficient theorem over
`F₂`** as a *natural isomorphism* — the Kronecker classifier
`kroneckerMap X n : Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)` is bijective
(`kroneckerMap_bijective`, `kroneckerEquiv`). Using it we reduce the
cohomology-transfer top nonvanishing to a **homology-side pairing** statement:

* `cohomologyMap_cocycleClass` / `cochainMap_preserves_cocycle` — generic facts
  about the homology of an arbitrary cochain map on a cocycle class (the
  generalization of `cohPullback_cocycleClass` from continuous-map pullbacks to
  the transfer cochain map).
* `cohTransferZMod2_ne_zero_iff_kronecker` — over `F₂` the transfer of a class is
  nonzero iff its Kronecker functional is nonzero (`kroneckerMap` is injective).
* `cohTransferZMod2_kronecker_adjunction` — the **transfer–Kronecker adjunction**
  `⟨tr c, z⟩ = ⟨c, tr_* z⟩` linking the cohomology transfer `cohTransferZMod2`
  and the homology transfer `projTransferHomologyZMod2` (the analogue, for the
  transfer chain map `projTransferChainMap`, of `kroneckerMap_naturality`).
* `cohTransferZMod2_top_ne_zero_of_homology_pairing` — Route A in usable form: if
  some `RPⁿ` homology class `z` has `⟨c, tr_* z⟩ ≠ 0`, then `tr c ≠ 0`.
* `TopHomologyTransferNonzeroWitness` — the **homology-side residual hypothesis**
  isolating exactly what is still missing, and
  `RPToSphereTransferTopNonzero_of_witness` — the genuine theorem that this
  residual hypothesis implies the full top-degree nonzero preservation
  `RPToSphereTransferTopNonzero n`.

## The residual blocker

The one remaining input, `TopHomologyTransferNonzeroWitness n`, is the
**homology-transfer nonvanishing on the top class** — equivalently, that the
homology transfer `projTransferHomologyZMod2 n n : Hₙ(RPⁿ; F₂) ⟶ Hₙ(Sⁿ; F₂)` is
nonzero, i.e. that it carries the `F₂`-fundamental class of `RPⁿ` to that of
`Sⁿ`. This is the geometric heart of the transfer (the sum of the two lifts of a
fundamental cycle of `RPⁿ` is a fundamental cycle of `Sⁿ`), and it is **not**
forced by the elementary covering identities (`p^* ∘ tr = 1 + τ^* = 0` and
`tr ∘ p_* = 2 = 0` over `F₂`). It requires `F₂`-fundamental classes of closed
manifolds together with the top-homology identification `Hₙ(Sⁿ; F₂) ≅ F₂`, both
of which are **absent from the pinned Mathlib** (the project carries
`Hₙ(Sⁿ; ℤ) ≅ ℤ` itself only as the bundled hypothesis `SphereOrientation` /
`SphereTopHomologyIso`, see `SphereTopHomology.lean`). See
`current/Transfer_Top_Class_Nonzero_Transfer_Result.md`.

Porting changes for Mathlib v4.32 (no statement is changed):

Every failure in this file was a `convert` that had been carrying dependent
`ModuleCat`/`forget₂` index equalities as extra goals; under v4.32 those goals
are no longer closed by the ambient `simp`s, and `convert` even left the
composition itself as a metavariable (`?convert_6 ≫ ?convert_7`). Each is
replaced by the categorical morphism equality it was approximating — the same
`ConcreteCategory.congr_hom` treatment already applied to
`CohomologyCupProduct`, whose `cohPullback_cocycleClass` is the green template
these proofs now follow:

* `cochainMap_preserves_cocycle`: `change` to the complex differential, rewrite
  along `D.comm n (n+1)` through `ModuleCat.comp_apply`, then `map_zero`.
* `cohomologyMap_cocycleClass`: `homologyπ_naturality` followed by a `calc` on
  cycles through `HomologicalComplex.cyclesMap_i` and `iCycles_cyclesMk`,
  replacing `simp; congr! 1; convert …; convert …`.
* `projTransferCochainMap_f_apply`: the transfer cochain map is precomposition,
  so this is exactly `ModuleCat.comp_apply` with both morphisms named; `convert`
  could not infer them.
* `projTransferHomologyZMod2_homologyπ`: rewrite along
  `projTransferHomologyZMod2_eq_homologyMap` and `homologyπ_naturality`.
* `cohTransferZMod2_ne_zero_iff_kronecker`: the two `simp_all` calls are now the
  explicit injectivity and `map_zero` steps.
* the tail of `cohTransferZMod2_kronecker_adjunction`: `cyclesMap_i` applied at
  `ζ` via `ConcreteCategory.congr_hom`, replacing a `congrArg` whose `simp only`
  made no progress.

The file also adopts the two definitional-equality compatibility options that
`CohomologyCupProduct` already sets, since these proofs `change` between
`cochainCoboundary` and the cochain complex's differential exactly as that
module does.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## Generic cochain-map facts on cocycle classes -/

/-
A cochain map `D : C^•(Y) ⟶ C^•(X)` carries cocycles to cocycles: if `φ` is a
cocycle then so is `D φ`. (Generalizes `cochainPullback_cocycle` from
continuous-map pullbacks to an arbitrary cochain map.)
-/
theorem cochainMap_preserves_cocycle {X Y : TopCat.{0}}
    (D : cochainCxZMod2 Y ⟶ cochainCxZMod2 X) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    cochainCoboundary (ZMod 2) X n ((D.f n).hom φ) = 0 := by
  have hcomm := D.comm n (n + 1)
  change ((cochainCxZMod2 X).d n (n + 1)).hom ((D.f n).hom φ) = 0
  rw [← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply]
  change (D.f (n + 1)).hom (cochainCoboundary (ZMod 2) Y n φ) = 0
  rw [hφ, map_zero]

/-
The homology of a cochain map `D : C^•(Y) ⟶ C^•(X)` on the class of a cocycle
`φ` is the class of the mapped cocycle `D φ`. (Generalizes
`cohPullback_cocycleClass`; here the cohomology map is `homologyMap D n`.)
-/
theorem cohomologyMap_cocycleClass {X Y : TopCat.{0}}
    (D : cochainCxZMod2 Y ⟶ cochainCxZMod2 X) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    (HomologicalComplex.homologyMap D n).hom (cocycleClass Y n φ hφ)
      = cocycleClass X n ((D.f n).hom φ) (cochainMap_preserves_cocycle D n φ hφ) := by
  unfold cocycleClass
  rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  apply congrArg ((cochainCxZMod2 X).homologyπ n).hom
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
  calc
    _ = (((cochainCxZMod2 Y).iCycles n ≫ D.f n).hom)
          ((cochainCxZMod2 Y).cyclesMk φ (n + 1) (by simp [ComplexShape.next]) hφ) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i D n) _
    _ = (D.f n).hom φ := by
      rw [ModuleCat.comp_apply, iCycles_cyclesMk]
    _ = _ := (iCycles_cyclesMk X n _ _).symm

/-! ## The transfer cochain map and its homology

The basic declarations `projTransferCochainMap` and
`cohTransferZMod2_eq_homologyMap` live in `CoveringTransferHomology`, alongside
the definition of `cohTransferZMod2` itself. -/

/-- `projTransferHomologyZMod2` is the homology of the transfer chain map. -/
theorem projTransferHomologyZMod2_eq_homologyMap (n k : ℕ) :
    projTransferHomologyZMod2 n k = HomologicalComplex.homologyMap (projTransferChainMap n) k := by
  rw [projTransferHomologyZMod2_eq]
  rfl

/-
Evaluation of the transfer cochain on a chain: `(tr* φ)(x) = φ(tr x)`
(the dualization is precomposition by the transfer chain map).
-/
theorem projTransferCochainMap_f_apply (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (Sphere n)) n)
    (x : (chainCxZMod2 (TopCat.of (RP n))).X n) :
    (((projTransferCochainMap n).f n).hom φ).hom x
      = φ.hom ((((projTransferChainMap n).f n)).hom x) :=
  ModuleCat.comp_apply ((projTransferChainMap n).f n) φ x

/-
The homology transfer on the class of a cycle `ζ` is the class of the
pushed-forward cycle `tr ζ` (naturality of `homologyπ`).
-/
theorem projTransferHomologyZMod2_homologyπ (n : ℕ)
    (ζ : (chainCxZMod2 (TopCat.of (RP n))).cycles n) :
    (projTransferHomologyZMod2 n n).hom
        (((chainCxZMod2 (TopCat.of (RP n))).homologyπ n).hom ζ)
      = ((chainCxZMod2 (TopCat.of (Sphere n))).homologyπ n).hom
          ((HomologicalComplex.cyclesMap (projTransferChainMap n) n).hom ζ) := by
  have key : (chainCxZMod2 (TopCat.of (RP n))).homologyπ n ≫ projTransferHomologyZMod2 n n
      = HomologicalComplex.cyclesMap (projTransferChainMap n) n
        ≫ (chainCxZMod2 (TopCat.of (Sphere n))).homologyπ n := by
    rw [projTransferHomologyZMod2_eq_homologyMap]
    exact HomologicalComplex.homologyπ_naturality (projTransferChainMap n) n
  exact ConcreteCategory.congr_hom key ζ

/-! ## Nonzero preservation, reduced to the homology side -/

/-- Over the field `F₂` the Kronecker classifier `kroneckerMap` is injective
(`kroneckerMap_injective`), so a transferred class is nonzero **iff** its
Kronecker functional is nonzero. -/
theorem cohTransferZMod2_ne_zero_iff_kronecker (n : ℕ) (c : sphereCohomology n n) :
    (cohTransferZMod2 n n).hom c ≠ 0
      ↔ (kroneckerMap (TopCat.of (RP n)) n).hom ((cohTransferZMod2 n n).hom c) ≠ 0 := by
  constructor <;> intro h <;> contrapose! h
  · exact kroneckerMap_injective _ _ (h.trans (map_zero _).symm)
  · rw [h, map_zero]

/-
**The transfer–Kronecker adjunction** `⟨tr c, z⟩ = ⟨c, tr_* z⟩`: pairing the
cohomology transfer `cohTransferZMod2` of a class `c ∈ Hⁿ(Sⁿ; F₂)` against an
`RPⁿ` homology class `z` equals pairing `c` against the homology transfer
`projTransferHomologyZMod2` of `z`. This is the analogue, for the transfer chain
map `projTransferChainMap`, of `kroneckerMap_naturality_apply`.
-/
theorem cohTransferZMod2_kronecker_adjunction (n : ℕ) (c : sphereCohomology n n)
    (z : homologyZMod2 (TopCat.of (RP n)) n) :
    (kroneckerMap (TopCat.of (RP n)) n).hom ((cohTransferZMod2 n n).hom c) z
      = (kroneckerMap (TopCat.of (Sphere n)) n).hom c
          ((projTransferHomologyZMod2 n n).hom z) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective (TopCat.of (Sphere n)) n c
  obtain ⟨ζ, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((chainCxZMod2 (TopCat.of (RP n))).homologyπ n)).1 inferInstance z
  -- Both sides reduce to `φ (tr (iCycles ζ))` via `kroneckerFunctional_apply`.
  have hL : (kroneckerMap (TopCat.of (RP n)) n).hom
        ((cohTransferZMod2 n n).hom (cocycleClass (TopCat.of (Sphere n)) n φ hφ))
        (((chainCxZMod2 (TopCat.of (RP n))).homologyπ n).hom ζ)
      = φ.hom (((projTransferChainMap n).f n).hom
          (((chainCxZMod2 (TopCat.of (RP n))).iCycles n).hom ζ)) := by
    have e1 : (cohTransferZMod2 n n).hom (cocycleClass (TopCat.of (Sphere n)) n φ hφ)
        = cocycleClass (TopCat.of (RP n)) n (((projTransferCochainMap n).f n).hom φ)
            (cochainMap_preserves_cocycle (projTransferCochainMap n) n φ hφ) := by
      rw [cohTransferZMod2_eq_homologyMap]
      exact cohomologyMap_cocycleClass (projTransferCochainMap n) n φ hφ
    rw [e1, kroneckerMap_cocycleClass, kroneckerFunctional_apply]
    exact projTransferCochainMap_f_apply n φ _
  have hR : (kroneckerMap (TopCat.of (Sphere n)) n).hom (cocycleClass (TopCat.of (Sphere n)) n φ hφ)
        ((projTransferHomologyZMod2 n n).hom
          (((chainCxZMod2 (TopCat.of (RP n))).homologyπ n).hom ζ))
      = φ.hom (((chainCxZMod2 (TopCat.of (Sphere n))).iCycles n).hom
          ((HomologicalComplex.cyclesMap (projTransferChainMap n) n).hom ζ)) := by
    rw [projTransferHomologyZMod2_homologyπ, kroneckerMap_cocycleClass, kroneckerFunctional_apply]
  rw [hL, hR]
  congr 1
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (projTransferChainMap n) n) ζ).symm

/-- **Route A in usable form.** If some `RPⁿ` homology class `z` pairs
nontrivially with `c` *after* the homology transfer, `⟨c, tr_* z⟩ ≠ 0`, then the
cohomology transfer of `c` is nonzero. -/
theorem cohTransferZMod2_top_ne_zero_of_homology_pairing (n : ℕ)
    (c : sphereCohomology n n) (z : homologyZMod2 (TopCat.of (RP n)) n)
    (h : (kroneckerMap (TopCat.of (Sphere n)) n).hom c
          ((projTransferHomologyZMod2 n n).hom z) ≠ 0) :
    (cohTransferZMod2 n n).hom c ≠ 0 := by
  rw [cohTransferZMod2_ne_zero_iff_kronecker]
  intro hzero
  apply h
  rw [← cohTransferZMod2_kronecker_adjunction]
  rw [hzero]
  rfl

/-- **The homology-side residual hypothesis.** For every nonzero top sphere class
`c`, some `RPⁿ` top homology class `z` pairs nontrivially with `c` after the
homology transfer. This is exactly the statement that the homology transfer
`projTransferHomologyZMod2 n n` is nonzero on the top class (carries the
`F₂`-fundamental class of `RPⁿ` to that of `Sⁿ`); see the module docstring and
`current/Transfer_Top_Class_Nonzero_Transfer_Result.md`. -/
def TopHomologyTransferNonzeroWitness (n : ℕ) : Prop :=
  ∀ c : sphereCohomology n n, c ≠ 0 →
    ∃ z : homologyZMod2 (TopCat.of (RP n)) n,
      (kroneckerMap (TopCat.of (Sphere n)) n).hom c
          ((projTransferHomologyZMod2 n n).hom z) ≠ 0

/-- **The reduction theorem.** The homology-side residual hypothesis
`TopHomologyTransferNonzeroWitness n` implies the full top-degree nonzero
preservation `RPToSphereTransferTopNonzero n` of the cohomology transfer. This is
the genuine content of Prompt 08: everything except the homology-transfer
nonvanishing on the fundamental class is discharged. -/
theorem RPToSphereTransferTopNonzero_of_witness (n : ℕ)
    (hw : TopHomologyTransferNonzeroWitness n) :
    RPToSphereTransferTopNonzero n := by
  intro c hc
  obtain ⟨z, hz⟩ := hw c hc
  exact cohTransferZMod2_top_ne_zero_of_homology_pairing n c z hz

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
