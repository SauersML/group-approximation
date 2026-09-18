import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Manuscript.NonMF.TorsionFreeOsinNotion
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull` and the paragraph after it, from the two least-area leaves

`non_mf_groups_exist.tex`, `thm:hull` (tex line 2122):

> Let $G$ be acylindrically hyperbolic, let $N\le G$ be suitable with respect
> to $A$, and let $g_1,\dots,g_m\in G$.  Then there is a surjective
> homomorphism $\varphi\colon G\to Q$ such that $Q$ is acylindrically
> hyperbolic, $\varphi(g_i)\in\varphi(N)$ for all $i$, and every element of
> finite order in $Q$ is the image of an element of the same order in $G$.

and the paragraph after it (tex line 2129):

> Hull's proof treats $m=1$ by passing to $G/\normal{r}_G$ for one element $r$
> and the general case by induction on $m$, using his clause (d), that
> $\varphi(N)$ is again suitable [proof of Theorem 7.1], so $\ker\varphi$ is the
> normal closure of $m$ elements and $Q$ is finitely presented when $G$ is.

## The route

Every endpoint below takes exactly two hypotheses, the least-area leaves:

* `leaf1 : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`
  (`GGT/VanKampen/Estimating/OsinAppendixSections.lean`), the least-area relative
  Greendlinger waist;
* `leaf2 : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`
  (`GGT/HullSCLemma51EmbeddedBridge.lean`), the embedded Lemma 5.1 bridge.

The chain from them to `thm:hull` is `HullSC.hullBallFormStatementGeneral_of_leastAreaLeaves`
(`GGT/HullSCTheorem71GeneralLeastArea.lean`):
`hullCanonicalQuotientStatementGeneral_of_boundedLemma44_of_lemma49` fed by

* `simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316 yiSuitableFiniteFamily_closed`
  (closed: DGO Proposition 4.14 is `dgoProposition414Uniform`);
* `boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea`, fed by `leaf2`
  and by `leaf1` through `relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger`
  with the closed `relativeDiscRealizationSpellingStatement` and
  `relativeExteriorArcConversionAtWordRotatedStatement`;
* `hullLemma49KernelPowerStatement_of_leastAreaGreendlinger leaf1`;

then `hullOneStepStatementGeneral_of_canonicalQuotient` (the case $m=1$, one relator),
`hullTowerStatementGeneral_of_oneStep` (the induction on $m$, through clause (d)
`HullStep.suitable_map`), and `hullBallFormStatementGeneral_of_tower`.  No other
`Statement` hypothesis occurs on the route: every other argument is a closed term.

The second leaf is itself closed, by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`,
so the `_of_greendlingerLeaf` forms below carry the least-area Greendlinger waist alone.

The paragraph's kernel and finite-presentation clauses are
`TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark`, unconditional on a tower.

Acylindrical hyperbolicity is stated both at Hull's Cayley-graph notion
(`TorsionFree.IsAcylindricallyHyperbolic`) and at Osin's
(`GGT.IsAcylindricallyHyperbolicOsin`); the two are equivalent by
`GGT.isAcylindricallyHyperbolic_of_osin` and `GGT.osin_of_isAcylindricallyHyperbolic`.
-/

namespace GroupApproximation
namespace GGT
namespace HullTheoremAssembly

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## `thm:hull` (tex line 2122) -/

/-- **`thm:hull`, as printed, from the two least-area leaves** (tex line 2122), at
Hull's Cayley-graph notion of acylindrical hyperbolicity. -/
theorem manuscriptSentence_hullTheorem_of_leaves
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (leaf2 :
      GroupApproximation.HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) {m : ℕ} (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      IsAcylindricallyHyperbolic Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
        ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y := by
  obtain ⟨H⟩ :=
    GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves
      leaf1 leaf2 A hN g
  exact ⟨H.Q, H.group, H.q, H.surjective, H.acylindricallyHyperbolic, H.mem_map,
    H.finiteOrder_lift⟩

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullTheorem_of_leaves

/-- **`thm:hull`, as printed, from the two least-area leaves** (tex line 2122), at
Osin's notion of acylindrical hyperbolicity, which the manuscript uses. -/
theorem manuscriptSentence_hullTheoremOsin_of_leaves
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (leaf2 :
      GroupApproximation.HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (G : Type) [Group G] (hG : GroupApproximation.GGT.IsAcylindricallyHyperbolicOsin G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) {m : ℕ}
    (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      GroupApproximation.GGT.IsAcylindricallyHyperbolicOsin Q ∧
        (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
          ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y := by
  haveI : IsAcylindricallyHyperbolic G :=
    GroupApproximation.GGT.isAcylindricallyHyperbolic_of_osin hG
  obtain ⟨Q, instQ, φ, hsurj, hah, hmem, hlift⟩ :=
    manuscriptSentence_hullTheorem_of_leaves leaf1 leaf2 A hN g
  exact ⟨Q, instQ, φ, hsurj,
    @GroupApproximation.GGT.osin_of_isAcylindricallyHyperbolic Q instQ hah, hmem, hlift⟩

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullTheoremOsin_of_leaves

/-! ## The paragraph after `thm:hull` (tex line 2129) -/

/-- **"Hull's proof treats $m=1$ by passing to $G/\normal{r}_G$ for one element
$r$"** (tex line 2129), from the two least-area leaves: for one target `t` the
quotient of `thm:hull` has kernel the normal closure of a single element `r`, and
is `G ⧸ ⟨⟨r⟩⟩`.  The generating set `A` already makes `G` acylindrically
hyperbolic (`HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet`). -/
theorem manuscriptSentence_hullOneTargetOneRelator_of_leaves
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (leaf2 :
      GroupApproximation.HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) (t : G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      IsAcylindricallyHyperbolic Q ∧ φ t ∈ N.map φ ∧
        (∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y) ∧
          ∃ r : G, φ.ker = Subgroup.normalClosure ({r} : Set G) ∧
            Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* Q) := by
  obtain ⟨s, r, hker, he⟩ :=
    GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves
      leaf1 leaf2 A hN t
  exact ⟨s.step.Q, s.step.group, s.step.q, s.step.surjective,
    GroupApproximation.HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet s.step.hullSet,
    s.mem_map 0, s.step.finiteOrder_lift, r, hker, he⟩

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullOneTargetOneRelator_of_leaves

/-- **"... and the general case by induction on $m$, using his clause (d), that
$\varphi(N)$ is again suitable, so $\ker\varphi$ is the normal closure of $m$
elements and $Q$ is finitely presented when $G$ is"** (tex line 2129), from the two
least-area leaves.  The quotient carries every clause of `thm:hull`, a Hull
generating set `B` for `Q` with respect to which `φ(N)` is suitable (clause (d)),
kernel the normal closure of at most `m` elements, and finite presentation
inherited from `G`. -/
theorem manuscriptSentence_hullInductionKernelFinitelyPresented_of_leaves
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (leaf2 :
      GroupApproximation.HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) {m : ℕ} (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q) (B : HullGeneratingSet Q),
      Function.Surjective φ ∧ IsAcylindricallyHyperbolic Q ∧
        (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
        (∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y) ∧
        Suitable B.alphabet (N.map φ) ∧
        (∃ T : Finset G, T.card ≤ m ∧ φ.ker = Subgroup.normalClosure (T : Set G)) ∧
        (Group.IsFinitelyPresented G → Group.IsFinitelyPresented Q) := by
  obtain ⟨s, hsuit⟩ :=
    GroupApproximation.Manuscript.NonMF.TorsionFreeHullParagraphGeneral.manuscriptSentence_hullInductionOnTargetsGeneral_of_leastAreaLeaves
      leaf1 leaf2 m A hN g 0
  obtain ⟨hker, hfp⟩ :=
    GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark
      s
  exact ⟨s.step.Q, s.step.group, s.step.q, s.step.hullSet, s.step.surjective,
    GroupApproximation.HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet s.step.hullSet,
    s.mem_map, s.step.finiteOrder_lift, hsuit, hker, hfp⟩

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullInductionKernelFinitelyPresented_of_leaves

/-! ## With the embedded bridge closed

`leaf2` is closed by `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`,
so each endpoint holds over the least-area Greendlinger waist alone. -/

/-- **`thm:hull`, as printed** (tex line 2122), over the least-area Greendlinger
waist alone. -/
theorem manuscriptSentence_hullTheorem_of_greendlingerLeaf
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] [IsAcylindricallyHyperbolic G] (A : HullGeneratingSet G)
    {N : Subgroup G} (hN : Suitable A.alphabet N) {m : ℕ} (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      IsAcylindricallyHyperbolic Q ∧ (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
        ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y :=
  manuscriptSentence_hullTheorem_of_leaves leaf1
    GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed A hN g

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullTheorem_of_greendlingerLeaf

/-- **`thm:hull`, as printed, at Osin's notion** (tex line 2122), over the
least-area Greendlinger waist alone. -/
theorem manuscriptSentence_hullTheoremOsin_of_greendlingerLeaf
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (G : Type) [Group G] (hG : GroupApproximation.GGT.IsAcylindricallyHyperbolicOsin G)
    (A : HullGeneratingSet G) {N : Subgroup G} (hN : Suitable A.alphabet N) {m : ℕ}
    (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      GroupApproximation.GGT.IsAcylindricallyHyperbolicOsin Q ∧
        (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
          ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y :=
  manuscriptSentence_hullTheoremOsin_of_leaves leaf1
    GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed G hG A hN g

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullTheoremOsin_of_greendlingerLeaf

/-- **The paragraph after `thm:hull`, $m=1$** (tex line 2129), over the least-area
Greendlinger waist alone. -/
theorem manuscriptSentence_hullOneTargetOneRelator_of_greendlingerLeaf
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) (t : G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
      IsAcylindricallyHyperbolic Q ∧ φ t ∈ N.map φ ∧
        (∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y) ∧
          ∃ r : G, φ.ker = Subgroup.normalClosure ({r} : Set G) ∧
            Nonempty (G ⧸ Subgroup.normalClosure ({r} : Set G) ≃* Q) :=
  manuscriptSentence_hullOneTargetOneRelator_of_leaves leaf1
    GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed A hN t

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullOneTargetOneRelator_of_greendlingerLeaf

/-- **The paragraph after `thm:hull`, general $m$** (tex line 2129), over the
least-area Greendlinger waist alone. -/
theorem manuscriptSentence_hullInductionKernelFinitelyPresented_of_greendlingerLeaf
    (leaf1 :
      GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    {G : Type} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    (hN : Suitable A.alphabet N) {m : ℕ} (g : Fin m → G) :
    ∃ (Q : Type) (_ : Group Q) (φ : G →* Q) (B : HullGeneratingSet Q),
      Function.Surjective φ ∧ IsAcylindricallyHyperbolic Q ∧
        (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
        (∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y) ∧
        Suitable B.alphabet (N.map φ) ∧
        (∃ T : Finset G, T.card ≤ m ∧ φ.ker = Subgroup.normalClosure (T : Set G)) ∧
        (Group.IsFinitelyPresented G → Group.IsFinitelyPresented Q) :=
  manuscriptSentence_hullInductionKernelFinitelyPresented_of_leaves leaf1
    GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed A hN g

#audit_axioms GroupApproximation.GGT.HullTheoremAssembly.manuscriptSentence_hullInductionKernelFinitelyPresented_of_greendlingerLeaf

end HullTheoremAssembly
end GGT
end GroupApproximation
