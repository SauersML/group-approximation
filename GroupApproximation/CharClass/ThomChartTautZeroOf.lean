import GroupApproximation.CharClass.ThomChartTautZero
import GroupApproximation.CharClass.ChernEulerIsoOf
import GroupApproximation.CharClass.LerayHirschChartClassGenK
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The tautological class vanishes on the affine chart, over a field

Lane `lx-stepcK-agree`.  The coefficient-`K` form of `CharClass/ThomChartTautZero.lean`.

The Thom class of `(E, E ∖ 0)` maps, across the bridge, to a Leray–Hirsch combination on
`P(E ⊕ 1)`, and restricting it to the affine chart `E ⊆ P(E ⊕ 1)` leaves only the bottom column
because the tautological class restricts to zero there.  Over `F₂` that is
`LH.pull_bridgeChartIncl_tautEulerOf`.  Over a field `K` the Euler class of a line takes its generator
as data (`eulerOfBundleOf K hgen`), and the dual class `ξ = e(O(1)) = −e(O(−1))` is the one the flag
relation and the Leray–Hirsch data over `K` use; both vanish on the chart, for every generator.

The argument is the `F₂` one word for word, and no step of it uses `1 = −1`:

* a line pulled back from a point has vanishing Euler class, since `H²` of a point is zero over any field;
* on the zero section the tautological line is the constant line (`Bundle.tautLineZeroSectionIso`), so its
  Euler class dies there;
* the chart is homotopy equivalent to the base with the zero section as homotopy inverse
  (`Bundle.chartOpensHomotopyEquivBase`), so the restriction to the chart is carried injectively onto the
  restriction to the zero section;
* the dual class is a negative, and a pullback is linear.

## Main declarations

* `eulerOfBundleOf_comap_const_eq_zero` — a line pulled back from a point has vanishing Euler class.
* `eulerOfBundleOf_pushforward_eq_zero_of_trivIso` — so does a line isomorphic to the trivial one.
* `LH.pull_zeroSectionProj_tautEulerOfK` — `e(O(−1))` dies on the zero section.
* `LH.pull_chartInclMap_tautEulerOfK`, `LH.pull_bridgeChartIncl_tautEulerOfK` — it dies on the chart.
* `LH.pull_bridgeChartIncl_tautEulerDualK` — **the dual class `ξ` dies on the chart**, the hypothesis
  `hξ` of the chart lemmas over `K` (`CharClass/ThomLIXHclassOf.lean`) at `ξ := tautEulerDualK K hgen p.plusOne`.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle

namespace GroupApproximation.CharClass

noncomputable section

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. A line pulled back from a point has vanishing Euler class -/

/-- **A line pulled back from a point has vanishing Euler class**, over a field and for every
generator.  Naturality moves the class onto the point, and `H²` of a point is zero. -/
theorem eulerOfBundleOf_comap_const_eq_zero (K : Type) [Field K] {N : ℕ}
    (hgen : Hmod K (CPtop N) 2) (Q : Bundle Unit (Fin (N + 1))) (hQ : ∀ y, (Q y).trace = 1) :
    eulerOfBundleOf K hgen (comap (ContinuousMap.const X (() : Unit)) Q)
        (fun x => hQ ((ContinuousMap.const X (() : Unit)) x)) = 0 := by
  rw [eulerOfBundle_comapOf K hgen Q hQ (ContinuousMap.const X (() : Unit))]
  have h := cohomology_unit_isZeroOf K 2 (by omega)
  rw [ModuleCat.isZero_iff_subsingleton] at h
  haveI := h
  have hz : eulerOfBundleOf K hgen Q hQ = 0 := Subsingleton.elim _ _
  rw [hz, pull_zero]

/-- **A line isomorphic to the trivial one has vanishing Euler class**, at any index it is pushed
into, over a field and for every generator. -/
theorem eulerOfBundleOf_pushforward_eq_zero_of_trivIso (K : Type) [Field K] {κ : Type} [Fintype κ]
    [DecidableEq κ] {N : ℕ} (hN : 1 ≤ N) (hgen : Hmod K (CPtop N) 2) (q : Bundle X κ)
    (e : BundleIso q (triv X (Fin 1))) {f : κ → Fin (N + 1)}
    (hf : Function.Injective f)
    (hfq : ∀ x, ((pushforward f hf q) x).trace = 1) :
    eulerOfBundleOf K hgen (pushforward f hf q) hfq = 0 := by
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
  rw [CPn.eulerOfBundle_pushforward_congrOf K hN hgen q (triv X (Fin 1)) hf hg hfq hgq e]
  exact eulerOfBundleOf_comap_const_eq_zero K hgen (pushforward _ hg (triv Unit (Fin 1)))
    (CPn.trace_pushforward_one _ hg (triv Unit (Fin 1)) htriv)

/-! ## 2. The class dies on the zero section -/

namespace LH

/-- **`e(O(−1))` restricts to zero on the zero section**, over a field and for every generator.  On
the zero section the tautological line is the constant line spanned by the `Unit` coordinate. -/
theorem pull_zeroSectionProj_tautEulerOfK (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf (ι ⊕ Unit))) 2) (p : Bundle X ι) :
    pull (cmap (zeroSectionProj p)) 2 (tautEulerOfK K hgen p.plusOne) = 0 := by
  have h := eulerOfBundle_comapOf K hgen
    (pushforward (tautEmbOf (ι ⊕ Unit)) (tautEmbOf_injective (ι ⊕ Unit))
      (tautLine p.plusOne))
    (CPn.trace_pushforward_one (tautEmbOf (ι ⊕ Unit)) (tautEmbOf_injective (ι ⊕ Unit))
      (tautLine p.plusOne) (trace_tautLine p.plusOne))
    (zeroSectionProj p)
  refine h.symm.trans ?_
  exact eulerOfBundleOf_pushforward_eq_zero_of_trivIso K
    (show 1 ≤ 1 + tautCardOf (ι ⊕ Unit) by omega) hgen
    (comap (zeroSectionProj p) (tautLine p.plusOne)) (tautLineZeroSectionIso p)
    (tautEmbOf_injective (ι ⊕ Unit)) _

/-! ## 3. The class dies on the affine chart -/

/-- **`e(O(−1))` restricts to zero on the affine chart**, in the subspace spelling, over a field and
for every generator.  The chart's homotopy inverse is the zero section. -/
theorem pull_chartInclMap_tautEulerOfK (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf (ι ⊕ Unit))) 2) (p : Bundle X ι) :
    pull (cmap (chartInclMap p)) 2 (tautEulerOfK K hgen p.plusOne) = 0 := by
  set e := chartOpensHomotopyEquivBase p
  have hround : ∀ a : Hmod K (TopCat.of ↥(chartOpensSet p)) 2,
      pull (cmap e.toFun) 2 (pull (cmap e.invFun) 2 a) = a := by
    intro a
    rw [← pull_comp,
      show (cmap e.toFun ≫ cmap e.invFun) = cmap (e.invFun.comp e.toFun) from rfl,
      pull_eq_of_homotopicOf K (f := cmap (e.invFun.comp e.toFun))
        (g := 𝟙 (TopCat.of ↥(chartOpensSet p))) e.left_inv 2 a, pull_id]
  have hmap : cmap e.invFun ≫ cmap (chartInclMap p) = cmap (zeroSectionProj p) := by
    apply TopCat.Hom.ext
    refine ContinuousMap.ext fun x => ?_
    exact chartOpensHomotopyEquivBase_invFun_apply p x
  have hzero : pull (cmap e.invFun) 2
      (pull (cmap (chartInclMap p)) 2 (tautEulerOfK K hgen p.plusOne)) = 0 := by
    rw [← pull_comp, hmap]
    exact pull_zeroSectionProj_tautEulerOfK K hgen p
  calc pull (cmap (chartInclMap p)) 2 (tautEulerOfK K hgen p.plusOne)
      = pull (cmap e.toFun) 2
          (pull (cmap e.invFun) 2 (pull (cmap (chartInclMap p)) 2 (tautEulerOfK K hgen p.plusOne))) :=
        (hround _).symm
    _ = pull (cmap e.toFun) 2 0 := by rw [hzero]
    _ = 0 := pull_zero _ _

/-- **`e(O(−1))` restricts to zero along the chart inclusion of the total space**, over a field and for
every generator. -/
theorem pull_bridgeChartIncl_tautEulerOfK (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf (ι ⊕ Unit))) 2) (p : Bundle X ι) :
    pull (cmap (bridgeChartIncl p)) 2 (tautEulerOfK K hgen p.plusOne) = 0 := by
  rw [bridgeChartIncl_eq p,
    show cmap ((chartInclMap p).comp (chartSymmMap p))
      = cmap (chartSymmMap p) ≫ cmap (chartInclMap p) from rfl,
    pull_comp, pull_chartInclMap_tautEulerOfK K hgen p, pull_zero]

/-- **The dual tautological class `ξ = e(O(1))` restricts to zero along the chart inclusion**, over a
field and for every generator.  This is the hypothesis `hξ` of the chart lemmas over `K` at
`ξ := tautEulerDualK K hgen p.plusOne`. -/
theorem pull_bridgeChartIncl_tautEulerDualK (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf (ι ⊕ Unit))) 2) (p : Bundle X ι) :
    pull (cmap (bridgeChartIncl p)) 2 (tautEulerDualK K hgen p.plusOne) = 0 := by
  have hneg := map_neg (pullLinear (K := K) (cmap (bridgeChartIncl p)) 2)
    (tautEulerOfK K hgen p.plusOne)
  have hz : pull (cmap (bridgeChartIncl p)) 2 (tautEulerOfK K hgen p.plusOne) = 0 :=
    pull_bridgeChartIncl_tautEulerOfK K hgen p
  show pull (cmap (bridgeChartIncl p)) 2 (-tautEulerOfK K hgen p.plusOne) = 0
  exact hneg.trans (neg_eq_zero.mpr hz)

end LH

end

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if it leaves the
classical allowlist. -/

#audit_axioms eulerOfBundleOf_comap_const_eq_zero
#audit_axioms eulerOfBundleOf_pushforward_eq_zero_of_trivIso
#audit_axioms LH.pull_zeroSectionProj_tautEulerOfK
#audit_axioms LH.pull_chartInclMap_tautEulerOfK
#audit_axioms LH.pull_bridgeChartIncl_tautEulerOfK
#audit_axioms LH.pull_bridgeChartIncl_tautEulerDualK

end GroupApproximation.CharClass
