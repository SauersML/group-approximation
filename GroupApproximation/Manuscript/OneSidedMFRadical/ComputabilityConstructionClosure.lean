import GroupApproximation.Computability.ParametricRecursiveSwitchPresentation
import GroupApproximation.Higman.BridgeEffectivity
import GroupApproximation.Higman.MikhailovaGraphProductWitness
import GroupApproximation.Higman.MikhailovaRopeCode
import GroupApproximation.Higman.MikhailovaRopeCompiler
import GroupApproximation.Higman.RopeTrick
import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Closed checkpoints for the manuscript's computability construction

This file packages the parts of the construction that are proved internally:

* a computable finite-seed switch with the required finite/infinite dichotomy;
* the group-theoretic embedding and three-generator clauses of the HNN bridge;
* the Mikhailova fibre product and the exact rank-three cutting subgroup;
* the product with a graph witness;
* the two HNN extensions of the rope trick, including the explicit finite
  presentation and the embedded quotient.

The propositions below quantify over all construction data internally.  Their
theorems therefore have no caller-supplied hypotheses, and the final commands
audit both closedness and the full axiom closure.

This module does not claim the two effectivity statements that remain open in
the current development: the presentation theorem for the HNN bridge and an
effective Higman embedding compiler from a recursive presentation to a finite
presentation with marked embedding words.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace ComputabilityConstruction

open GroupApproximation.Higman

/-! ## The switch -/

/-- The existing compiler is computable jointly in a finite-presentation seed
and a partial-recursive program, and its carrier is trivial on the infinite
branch and isomorphic to the seed on the finite branch. -/
def PrintedParametricSwitchPackage : Prop :=
  Computable₂
      ParametricRecursiveSwitchPresentation.parametricSwitchEnumeratorCode ∧
    ∀ (seed : PresentationCodes.PresentationCode) (c : Nat.Partrec.Code),
      (SecondLevelIndexSets.InfiniteDomain c →
        Subsingleton
          (ParametricRecursiveSwitchPresentation.ParametricCompiledCarrier
            seed c)) ∧
      (SecondLevelIndexSets.InfiniteDomain c →
        Nonempty
          (ParametricRecursiveSwitchPresentation.ParametricCompiledCarrier
              seed c ≃* PUnit.{1})) ∧
      (SecondLevelIndexSets.FiniteDomain c →
        Nonempty
          (ParametricRecursiveSwitchPresentation.ParametricCompiledCarrier
              seed c ≃* PresentationCodes.Carrier seed)) ∧
      ((SecondLevelIndexSets.InfiniteDomain c ∧
          Nonempty
            (ParametricRecursiveSwitchPresentation.ParametricCompiledCarrier
                seed c ≃* PUnit.{1})) ∨
        (SecondLevelIndexSets.FiniteDomain c ∧
          Nonempty
            (ParametricRecursiveSwitchPresentation.ParametricCompiledCarrier
                seed c ≃* PresentationCodes.Carrier seed)))

theorem manuscriptPrintedParametricSwitchPackage :
    PrintedParametricSwitchPackage := by
  refine ⟨ParametricRecursiveSwitchPresentation.computable₂_parametricSwitchEnumeratorCode,
    ?_⟩
  intro seed c
  exact
    ⟨ParametricRecursiveSwitchPresentation.compiledCarrier_subsingleton_of_infiniteDomain
        seed c,
      ParametricRecursiveSwitchPresentation.compiledCarrier_equiv_punit_of_infiniteDomain
        seed c,
      ParametricRecursiveSwitchPresentation.compiledCarrier_equiv_seed_of_finiteDomain
        seed c,
      ParametricRecursiveSwitchPresentation.compiled_two_isomorphism_types seed c⟩

/-! ## The bridge -/

/-- The group-theoretic part of the three-generator bridge: the original group
embeds, and a spanning generating family makes the three displayed elements
generate the HNN extension. -/
def PrintedBridgeGroupTheoryPackage : Prop :=
  ∀ (A : Type) [Group A] (g : ℕ → A),
    Function.Injective (Higman.HNNEmb.embA g) ∧
      (Subgroup.closure (Set.range g) = ⊤ →
        Subgroup.closure (Higman.HNNEmb.gens g) = ⊤) ∧
      (Subgroup.closure (Set.range g) = ⊤ →
        Function.Surjective (Higman.BridgeEff.pi3 g))

theorem manuscriptPrintedBridgeGroupTheoryPackage :
    PrintedBridgeGroupTheoryPackage := by
  intro A _ g
  exact ⟨Higman.HNNEmb.embA_injective g,
    Higman.BridgeEff.closure_gens_eq_top_of_spans g,
    Higman.BridgeEff.pi3_surjective g⟩

/-! ## The Mikhailova subgroup -/

/-- For a finite alphabet and finite relator set, the displayed Mikhailova
subgroup is finitely generated and equals the fibre product of the quotient
map with itself. -/
def PrintedMikhailovaFiberProductPackage : Prop :=
  ∀ (X : Type) [Finite X] (R : Set (FreeGroup X)), R.Finite →
    (Higman.Mikhailova.freeSubgroup R).FG ∧
      Higman.Mikhailova.freeSubgroup R =
        Higman.Mikhailova.fiberProduct R ∧
      ∀ u v : FreeGroup X,
        ((u, v) ∈ Higman.Mikhailova.freeSubgroup R ↔
          PresentedGroup.mk R u = PresentedGroup.mk R v)

theorem manuscriptPrintedMikhailovaFiberProductPackage :
    PrintedMikhailovaFiberProductPackage := by
  intro X _ R hR
  exact ⟨Higman.Mikhailova.freeSubgroup_fg hR,
    Higman.Mikhailova.freeSubgroup_eq_fiberProduct R,
    Higman.Mikhailova.mem_freeSubgroup_iff_presented_mk_eq R⟩

/-- Finite marked embedding data give the exact rank-three cutting subgroup:
the source map is injective, the cutting subgroup is finitely generated, its
pullback is the source normal closure, and the corresponding ambient
intersection is its image. -/
def PrintedRankThreeCutPackage : Prop :=
  ∀ (X : Type) [Finite X]
    (S : Set Higman.MikhailovaRankThree.Source)
    (R : Set (FreeGroup X)) (_hR : R.Finite),
    ∀ (words : Higman.MikhailovaRankThree.Source →* FreeGroup X)
      (i : PresentedGroup S →* PresentedGroup R)
      (_hi : Function.Injective i)
      (_hcomm : (Higman.MikhailovaRankThree.quotientHom R).comp words =
        i.comp (Higman.MikhailovaRankThree.quotientHom S)),
      Function.Injective (Higman.MikhailovaRankThree.inputHom words) ∧
        (Higman.MikhailovaRankThree.cuttingSubgroup R).FG ∧
        (Higman.MikhailovaRankThree.cuttingSubgroup R).comap
            (Higman.MikhailovaRankThree.inputHom words) =
          Subgroup.normalClosure S ∧
        (Higman.MikhailovaRankThree.inputHom words).range ⊓
            Higman.MikhailovaRankThree.cuttingSubgroup R =
          (Subgroup.normalClosure S).map
            (Higman.MikhailovaRankThree.inputHom words)

theorem manuscriptPrintedRankThreeCutPackage :
    PrintedRankThreeCutPackage := by
  intro X _ S R hR words i hi hcomm
  exact ⟨Higman.MikhailovaRankThree.inputHom_injective words,
    Higman.MikhailovaRankThree.cuttingSubgroup_fg hR,
    (Higman.MikhailovaRankThree.comap_cutting_eq_kernel R words).trans
      (Higman.MikhailovaRankThree.kernel_eq_normalClosure_of_markedEmbedding
        S R words i hi hcomm),
    Higman.MikhailovaRankThree.range_inf_cutting_eq_normalClosure_map
      S R words i hi hcomm⟩

/-! ## Producting with the graph witness -/

/-- If the graph homomorphism kills the source normal closure, producting its
graph witness with the Mikhailova witness leaves the cut unchanged. -/
def PrintedMikhailovaGraphProductPackage : Prop :=
  ∀ (X P : Type) [Finite X] [Group P] [Group.IsFinitelyPresented P]
    (S : Set Higman.MikhailovaRankThree.Source)
    (R : Set (FreeGroup X)) (hR : R.Finite),
    ∀ (words : Higman.MikhailovaRankThree.Source →* FreeGroup X)
      (i : PresentedGroup S →* PresentedGroup R)
      (hi : Function.Injective i)
      (hcomm : (Higman.MikhailovaRankThree.quotientHom R).comp words =
        i.comp (Higman.MikhailovaRankThree.quotientHom S))
      (q : Higman.MikhailovaRankThree.Source →* P)
      (hSq : Subgroup.normalClosure S ≤ q.ker),
        let w := Higman.MikhailovaGraphProduct.normalClosureProductWitness
          S hR words i hi hcomm q hSq
        Function.Injective w.emb ∧ w.L.FG ∧
          w.L.comap w.emb = Subgroup.normalClosure S

theorem manuscriptPrintedMikhailovaGraphProductPackage :
    PrintedMikhailovaGraphProductPackage := by
  intro X P _ _ _ S R hR words i hi hcomm q hSq
  let w := Higman.MikhailovaGraphProduct.normalClosureProductWitness
    S hR words i hi hcomm q hSq
  exact ⟨w.emb_injective, w.L_fg, w.comap_eq⟩

/-- The marked Mikhailova cut and its graph factor feed directly into the rope
trick, giving a finitely presented overgroup of the source quotient. -/
def PrintedMikhailovaRopeCompositionPackage : Prop :=
  ∀ (X P : Type) [Finite X] [Group P] [Group.IsFinitelyPresented P]
    (S : Set Higman.MikhailovaRankThree.Source)
    (R : Set (FreeGroup X)) (_hR : R.Finite)
    (words : Higman.MikhailovaRankThree.Source →* FreeGroup X)
    (i : PresentedGroup S →* PresentedGroup R)
    (_hi : Function.Injective i)
    (_hcomm : (Higman.MikhailovaRankThree.quotientHom R).comp words =
      i.comp (Higman.MikhailovaRankThree.quotientHom S))
    (q : Higman.MikhailovaRankThree.Source →* P)
    (_hSq : Subgroup.normalClosure S ≤ q.ker),
    Nonempty (Higman.FPOvergroup (PresentedGroup S))

theorem manuscriptPrintedMikhailovaRopeCompositionPackage :
    PrintedMikhailovaRopeCompositionPackage := by
  intro X P _ _ _ S R hR words i hi hcomm q hSq
  exact Higman.MikhailovaRopeCompiler.nonempty_fpOvergroup_of_markedEmbedding_and_graph
    S hR words i hi hcomm q hSq

/-- Once the finite ambient, source, cutting words, and marked words have been
computed, the remaining raw finite-presentation transformation is computable. -/
def PrintedRawRopeSyntaxCompilerIsComputable : Prop :=
  Computable Higman.MikhailovaRopeCode.compile

theorem manuscriptPrintedRawRopeSyntaxCompilerIsComputable :
    PrintedRawRopeSyntaxCompilerIsComputable :=
  Higman.MikhailovaRopeCode.computable_compile

/-! ## The ropes -/

/-- Every benign normal subgroup of a finitely generated, finitely presented
group gives the manuscript's two-rope group.  The first HNN extension is
finitely presented, the quotient embeds in the second, and the second is
isomorphic to an explicit finite presentation. -/
def PrintedRopePackage : Prop :=
  ∀ (F : Type) [Group F] [Group.IsFinitelyPresented F] [Group.FG F]
    (N : Subgroup F) [N.Normal] (w : Higman.BenignWitness N),
    Group.IsFinitelyPresented (Higman.Rope.Gamma w) ∧
      Function.Injective (Higman.Rope.quotientEmb w) ∧
      ∃ SF : Set F, SF.Finite ∧ Subgroup.closure SF = ⊤ ∧
        Nonempty
          (Higman.Rope.Pres w SF ≃* Higman.Rope.RopeGroup w) ∧
        Group.IsFinitelyPresented (Higman.Rope.RopeGroup w)

theorem manuscriptPrintedRopePackage : PrintedRopePackage := by
  intro F _ _ _ N _ w
  refine ⟨Higman.Rope.isFinitelyPresented_gamma w,
    Higman.Rope.quotientEmb_injective w, ?_⟩
  obtain ⟨SF, hSF, hSFfin⟩ :=
    Group.fg_iff.mp (inferInstance : Group.FG F)
  letI : Group.IsFinitelyPresented (Higman.Rope.RopeGroup w) :=
    Higman.Rope.isFinitelyPresented_ropeGroup w SF hSFfin hSF
  exact ⟨SF, hSFfin, hSF, ⟨Higman.Rope.ropeEquiv w SF hSF⟩, inferInstance⟩

/-! ## The negative branch -/

/-- The final implication in the finite branch, stated independently of the
particular compiler: a countable group containing a countable non-MF group
through an injective homomorphism cannot be MF. -/
def PrintedNonMFEmbeddingObstruction : Prop :=
  ∀ (H R : Type) [Group H] [Group R] [Countable H] [Countable R],
    ¬ IsOperatorMF H →
      ∀ i : H →* R, Function.Injective i → ¬ IsOperatorMF R

/-- **The manuscript's negative-branch heredity argument.**  Restricting an
operator-MF corona representation along the displayed embedding would make the
source operator-MF, contradicting the hypothesis. -/
theorem manuscriptPrintedNonMFEmbeddingObstruction :
    PrintedNonMFEmbeddingObstruction := by
  intro H R _ _ _ _ hH i hi hR
  exact hH (hR.comap i hi)

#audit_closed_axioms manuscriptPrintedParametricSwitchPackage
#audit_closed_axioms manuscriptPrintedBridgeGroupTheoryPackage
#audit_closed_axioms manuscriptPrintedMikhailovaFiberProductPackage
#audit_closed_axioms manuscriptPrintedRankThreeCutPackage
#audit_closed_axioms manuscriptPrintedMikhailovaGraphProductPackage
#audit_closed_axioms manuscriptPrintedMikhailovaRopeCompositionPackage
#audit_closed_axioms manuscriptPrintedRawRopeSyntaxCompilerIsComputable
#audit_closed_axioms manuscriptPrintedRopePackage
#audit_closed_axioms manuscriptPrintedNonMFEmbeddingObstruction

end ComputabilityConstruction
end OneSidedMFRadical
end Manuscript
end GroupApproximation
