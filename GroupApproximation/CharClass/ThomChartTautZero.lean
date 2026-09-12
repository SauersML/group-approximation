import GroupApproximation.CharClass.ThomBridgeNatural
import GroupApproximation.CharClass.BundleTautPieces
import GroupApproximation.CharClass.ChernTautRestrict
import GroupApproximation.CharClass.LerayHirschChartClassGen
import GroupApproximation.CharClass.CohomologyBridge
import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The tautological class vanishes on the affine chart

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

This is the one piece of geometry in `hclass`.  The Thom class of `(E, E ∖ 0)`
maps, across the bridge, to a Leray–Hirsch combination `∑_i π^*(a_i) ⌣ ξ^i` on
`P(E ⊕ 1)`; restricting it to the affine chart `E ⊆ P(E ⊕ 1)` must leave only the
`i = 0` column, and the reason is that **`ξ` restricts to zero on the chart**.

The classical reason is that the tautological line has the nowhere-zero section
`v ↦ (v, 1)` over the chart.  Here the section never appears: `cc-bundle` already
proved that the chart is homotopy equivalent to the base with the **zero section**
as a homotopy inverse (`chartOpensHomotopyEquivBase_invFun_apply`), and that on
the zero section the tautological line is the constant line `infPoint`
(`tautLineZeroSectionIso`).  A constant line is pulled back from a point, and a
point has no `H^2`.  So the vanishing is homotopy invariance plus the two facts
`cc-bundle` already published, and no new bundle map is constructed.

## What this does not do

It says nothing about `ξ` on the complement of the zero section, where it is not
zero and where the Gysin sequence lives.  And it is a statement about the
**class**, not about the tautological line itself: the line is not trivial over
the chart on the nose, only up to the homotopy that contracts the chart.

## Main declarations

* `eulerOfBundle_comap_const_eq_zero` — a line pulled back from a point has
  vanishing Euler class.
* `LH.pull_zeroSectionProj_tautEulerOf` — `ξ` dies on the zero section.
* `LH.pull_bridgeChartIncl_tautEulerOf` — **`ξ` dies on the affine chart**, in
  the spelling `bridgeTotal` is built from.
* `bridgeChartIncl_comp_projMapOf` — the chart inclusion lies over the base.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle

namespace GroupApproximation.CharClass

noncomputable section

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. A bundle pulled back from a point has vanishing Euler class -/

/-- **A line pulled back from a point has vanishing Euler class.**  Naturality
moves the class onto the point, and `H^2` of a point is zero. -/
theorem eulerOfBundle_comap_const_eq_zero {N : ℕ} (hN : 1 ≤ N)
    (Q : Bundle Unit (Fin (N + 1))) (hQ : ∀ y, (Q y).trace = 1) :
    eulerOfBundle hN (comap (ContinuousMap.const X (() : Unit)) Q)
        (fun x => hQ ((ContinuousMap.const X (() : Unit)) x)) = 0 := by
  rw [eulerOfBundle_comap hN Q hQ (ContinuousMap.const X (() : Unit))]
  have h := cohomology_unit_isZero 2 (by omega)
  rw [ModuleCat.isZero_iff_subsingleton] at h
  haveI := h
  have hz : eulerOfBundle hN Q hQ = 0 := Subsingleton.elim _ _
  rw [hz, pull_zero]

/-- **A line isomorphic to the trivial one has vanishing Euler class**, at any
index it is pushed into.  The trivial line is pulled back from a point, so this
is the previous lemma once the representative is changed. -/
theorem eulerOfBundle_pushforward_eq_zero_of_trivIso {κ : Type} [Fintype κ]
    [DecidableEq κ] {N : ℕ} (hN : 1 ≤ N) (q : Bundle X κ)
    (e : BundleIso q (triv X (Fin 1))) {f : κ → Fin (N + 1)}
    (hf : Function.Injective f)
    (hfq : ∀ x, ((pushforward f hf q) x).trace = 1) :
    eulerOfBundle hN (pushforward f hf q) hfq = 0 := by
  have hg : Function.Injective (fun _ : Fin 1 => (0 : Fin (N + 1))) :=
    fun a b _ => Subsingleton.elim a b
  have htriv : ∀ y : Unit, ((triv Unit (Fin 1)) y).trace = 1 := by
    intro _
    show (1 : Matrix (Fin 1) (Fin 1) ℂ).trace = 1
    simp
  have htrX : ∀ x : X, ((triv X (Fin 1)) x).trace = 1 := by
    intro _
    show (1 : Matrix (Fin 1) (Fin 1) ℂ).trace = 1
    simp
  have hgq : ∀ x : X, ((pushforward _ hg (triv X (Fin 1))) x).trace = 1 :=
    CPn.trace_pushforward_one _ hg (triv X (Fin 1)) htrX
  rw [CPn.eulerOfBundle_pushforward_congr hN q (triv X (Fin 1)) hf hg hfq hgq e]
  exact eulerOfBundle_comap_const_eq_zero hN (pushforward _ hg (triv Unit (Fin 1)))
    (CPn.trace_pushforward_one _ hg (triv Unit (Fin 1)) htriv)

/-! ## 2. The class dies on the zero section -/

namespace LH

/-- **`ξ` restricts to zero on the zero section.**  On the zero section the
tautological line is the constant line spanned by the `Unit` coordinate, which is
`cc-bundle`'s `tautLineZeroSectionIso`. -/
theorem pull_zeroSectionProj_tautEulerOf (p : Bundle X ι) :
    pull (cmap (zeroSectionProj p)) 2 (tautEulerOf p.plusOne) = 0 := by
  have h := eulerOfBundle_comap (show 1 ≤ 1 + tautCardOf (ι ⊕ Unit) by omega)
    (pushforward (tautEmbOf (ι ⊕ Unit)) (tautEmbOf_injective (ι ⊕ Unit))
      (tautLine p.plusOne))
    (CPn.trace_pushforward_one (tautEmbOf (ι ⊕ Unit)) (tautEmbOf_injective (ι ⊕ Unit))
      (tautLine p.plusOne) (trace_tautLine p.plusOne))
    (zeroSectionProj p)
  refine h.symm.trans ?_
  exact eulerOfBundle_pushforward_eq_zero_of_trivIso
    (show 1 ≤ 1 + tautCardOf (ι ⊕ Unit) by omega)
    (comap (zeroSectionProj p) (tautLine p.plusOne)) (tautLineZeroSectionIso p)
    (tautEmbOf_injective (ι ⊕ Unit)) _

/-! ## 3. The class dies on the affine chart -/

end LH

/-- The affine chart, as a map into the projectivisation. -/
def chartInclMap (p : Bundle X ι) : C(↥(chartOpensSet p), Proj p.plusOne) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The chart identification, as a map out of the total space. -/
def chartSymmMap (p : Bundle X ι) : C(Total p, ↥(chartOpensSet p)) :=
  ⟨(chartOpensHomeoTotal p).symm, (chartOpensHomeoTotal p).symm.continuous⟩

/-- `bridgeChartIncl` is the chart identification followed by the inclusion. -/
theorem bridgeChartIncl_eq (p : Bundle X ι) :
    bridgeChartIncl p = (chartInclMap p).comp (chartSymmMap p) :=
  ContinuousMap.ext fun _ => rfl

namespace LH

/-- **`ξ` restricts to zero on the affine chart**, in the subspace spelling.  The
chart's homotopy inverse is the zero section, so the restriction to the chart is
carried by an injection onto the restriction to the zero section, which is zero. -/
theorem pull_chartInclMap_tautEulerOf (p : Bundle X ι) :
    pull (cmap (chartInclMap p)) 2 (tautEulerOf p.plusOne) = 0 := by
  set e := chartOpensHomotopyEquivBase p
  have hround : ∀ a : Hmod2 (TopCat.of ↥(chartOpensSet p)) 2,
      pull (cmap e.toFun) 2 (pull (cmap e.invFun) 2 a) = a := by
    intro a
    rw [← pull_comp,
      show (cmap e.toFun ≫ cmap e.invFun) = cmap (e.invFun.comp e.toFun) from rfl,
      pull_eq_of_homotopic (f := cmap (e.invFun.comp e.toFun))
        (g := 𝟙 (TopCat.of ↥(chartOpensSet p))) e.left_inv 2 a, pull_id]
  have hmap : cmap e.invFun ≫ cmap (chartInclMap p) = cmap (zeroSectionProj p) := by
    apply TopCat.Hom.ext
    refine ContinuousMap.ext fun x => ?_
    exact chartOpensHomotopyEquivBase_invFun_apply p x
  have hzero : pull (cmap e.invFun) 2
      (pull (cmap (chartInclMap p)) 2 (tautEulerOf p.plusOne)) = 0 := by
    rw [← pull_comp, hmap]
    exact pull_zeroSectionProj_tautEulerOf p
  calc pull (cmap (chartInclMap p)) 2 (tautEulerOf p.plusOne)
      = pull (cmap e.toFun) 2
          (pull (cmap e.invFun) 2 (pull (cmap (chartInclMap p)) 2 (tautEulerOf p.plusOne))) :=
        (hround _).symm
    _ = pull (cmap e.toFun) 2 0 := by rw [hzero]
    _ = 0 := pull_zero _ _

/-- **`ξ` restricts to zero along the chart inclusion of the total space**, which
is the map `bridgeTotal` is built from. -/
theorem pull_bridgeChartIncl_tautEulerOf (p : Bundle X ι) :
    pull (cmap (bridgeChartIncl p)) 2 (tautEulerOf p.plusOne) = 0 := by
  rw [bridgeChartIncl_eq p,
    show cmap ((chartInclMap p).comp (chartSymmMap p))
      = cmap (chartSymmMap p) ≫ cmap (chartInclMap p) from rfl,
    pull_comp, pull_chartInclMap_tautEulerOf, pull_zero]

end LH

/-! ## 4. The chart inclusion lies over the base -/

/-- **The chart inclusion lies over the base.**  `chartOf` divides the matrix
entries and leaves the base point alone, so both sides read the same coordinate. -/
theorem bridgeChartIncl_comp_projMapOf (p : Bundle X ι) :
    cmap (bridgeChartIncl p) ≫ projMapOf p.plusOne = cmap (totalPi p) := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the
build** if it leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms LH.pull_bridgeChartIncl_tautEulerOf

end

end GroupApproximation.CharClass
