import GroupApproximation.Computability.AdianRabinGeneral
import GroupApproximation.Computability.OperatorMFMarkovData
import GroupApproximation.Computability.ParametricRecursiveSwitchPresentation
import GroupApproximation.Computability.PresentationCodeCompleteness

/-!
# Second-level completeness for hereditary group properties

The parameterized event-ray compiler takes an arbitrary finite-presentation
seed.  Its infinite-domain branch is trivial and its finite-domain branch is
exactly the seed group.  Consequently every subgroup-hereditary property that
holds for the trivial group and fails for the seed is `Π⁰₂`-complete on
the compiled family.  Its complement is `Σ⁰₂`-complete, and both sides
are globally hard on standard enumerated-presentation codes.

The finite-presentation-code statements at the end are deliberately
conditional on an explicit finite-output compiler.  The event-ray compiler
constructed in this repository emits standard recursively enumerated
presentations, not finite presentations.
-/

namespace GroupApproximation
namespace HereditaryPropertySwitchCompleteness

open Nat.Partrec
open ArithmeticalHierarchy
open SecondLevelIndexSets
open PresentationCodes
open ParametricRecursiveSwitchPresentation

noncomputable section

/-! ## Minimal property data -/

/-- The exact property data consumed by the two-branch switch.

Unlike the full Adian--Rabin interface, the switch needs no closure on all free
groups and no separate positive presentation code. -/
structure SwitchPropertyData (P : (H : Type) → [Group H] → Prop) where
  /-- The property passes to groups which inject into a group having it. -/
  hereditary : ∀ {H K : Type} [Group H] [Group K] (f : H →* K),
    Function.Injective f → P K → P H
  /-- The positive branch: the trivial group has the property. -/
  trivial : P PUnit
  /-- A finite-presentation code for the negative branch. -/
  forbidden : PresentationCode
  /-- The seed group fails the property. -/
  forbidden_not : ¬ P (Carrier forbidden)

variable {P : (H : Type) → [Group H] → Prop}

/-- The property induced on standard recursively enumerated presentation
codes. -/
def EnumeratedCodeProperty (P : (H : Type) → [Group H] → Prop)
    (c : Code) : Prop :=
  P (EnumeratedPresentationCodes.Carrier c)

/-- The property restricted to the computable switch family selected by
`D.forbidden`. -/
def RestrictedProperty (D : SwitchPropertyData P) (c : Code) : Prop :=
  P (ParametricCompiledCarrier D.forbidden c)

/-- The complementary restricted property. -/
def RestrictedComplement (D : SwitchPropertyData P) (c : Code) : Prop :=
  ¬ RestrictedProperty D c

/-- The standard-code compiler selected by the forbidden seed. -/
abbrev compile (D : SwitchPropertyData P) (c : Code) : Code :=
  parametricSwitchEnumeratorCode D.forbidden c

/-- Fixing the finite seed in the jointly computable compiler leaves a
computable transformation of source programs. -/
theorem computable_compile (D : SwitchPropertyData P) :
    Computable (compile D) :=
  computable₂_parametricSwitchEnumeratorCode.comp
    (Computable.const D.forbidden) Computable.id

/-- Heredity already supplies the direction of isomorphism invariance used by
the switch proofs. -/
theorem SwitchPropertyData.of_mulEquiv (D : SwitchPropertyData P)
    {H K : Type} [Group H] [Group K] (e : H ≃* K) (hK : P K) : P H :=
  D.hereditary e.toMonoidHom e.injective hK

/-! ## Exact truth table -/

/-- The property holds on a compiled carrier exactly when the source program
has infinite domain. -/
theorem restrictedProperty_iff_infiniteDomain
    (D : SwitchPropertyData P) (c : Code) :
    RestrictedProperty D c ↔ InfiniteDomain c := by
  constructor
  · intro hP
    by_contra hinfinite
    have hfinite : FiniteDomain c := by
      simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hinfinite
    obtain ⟨e⟩ := compiledCarrier_equiv_seed_of_finiteDomain
      D.forbidden c hfinite
    exact D.forbidden_not
      (D.hereditary e.symm.toMonoidHom e.symm.injective hP)
  · intro hinfinite
    obtain ⟨e⟩ := compiledCarrier_equiv_punit_of_infiniteDomain
      D.forbidden c hinfinite
    exact D.hereditary e.toMonoidHom e.injective D.trivial

/-- The complementary property holds exactly when the source domain is
finite. -/
theorem restrictedComplement_iff_finiteDomain
    (D : SwitchPropertyData P) (c : Code) :
    RestrictedComplement D c ↔ FiniteDomain c := by
  have h := not_congr (restrictedProperty_iff_infiniteDomain D c)
  simpa only [RestrictedComplement, FiniteDomain, InfiniteDomain,
    Set.not_infinite] using h

/-! ## Restricted completeness -/

/-- The property is `Π⁰₂`-complete on the arbitrary-seed switch family. -/
theorem restrictedProperty_pi02Complete (D : SwitchPropertyData P) :
    Pi02Complete (RestrictedProperty D) := by
  constructor
  · exact (pi02_congr (restrictedProperty_iff_infiniteDomain D)).2
      infiniteDomain_pi02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
    exact ⟨f, hf, fun n ↦
      (hcorrect n).trans
        (restrictedProperty_iff_infiniteDomain D (f n)).symm⟩

/-- The complementary property is `Σ⁰₂`-complete on the same family. -/
theorem restrictedComplement_sigma02Complete (D : SwitchPropertyData P) :
    Sigma02Complete (RestrictedComplement D) :=
  pi02Complete_compl (restrictedProperty_pi02Complete D)

/-! ## Global hardness on standard enumerated presentations -/

/-- Global recognition of the property is `Π⁰₂`-hard.  This is a
hardness theorem only; it asserts no global upper bound. -/
theorem enumeratedCodeProperty_pi02Hard (D : SwitchPropertyData P) :
    Pi02Hard (EnumeratedCodeProperty P) := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  refine ⟨fun n ↦ compile D (f n), (computable_compile D).comp hf,
    fun n ↦ ?_⟩
  exact (hcorrect n).trans
    (restrictedProperty_iff_infiniteDomain D (f n)).symm

/-- Global recognition of failure of the property is `Σ⁰₂`-hard. -/
theorem enumeratedCodeProperty_compl_sigma02Hard
    (D : SwitchPropertyData P) :
    Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) :=
  pi02Hard_compl (enumeratedCodeProperty_pi02Hard D)

/-- Closed arbitrary-code endpoint supplied by one switch datum. -/
theorem switch_completeness_package (D : SwitchPropertyData P) :
    Pi02Complete (RestrictedProperty D) ∧
      Sigma02Complete (RestrictedComplement D) ∧
      Pi02Hard (EnumeratedCodeProperty P) ∧
      Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) :=
  ⟨restrictedProperty_pi02Complete D,
    restrictedComplement_sigma02Complete D,
    enumeratedCodeProperty_pi02Hard D,
    enumeratedCodeProperty_compl_sigma02Hard D⟩

/-! ## Adapters -/

/-- Full Adian--Rabin Markov data contains the smaller switch interface.
Truth on `PUnit` follows from truth on the free group on the empty alphabet. -/
noncomputable def SwitchPropertyData.ofMarkovData
    (D : AdianRabinGeneral.MarkovData P) : SwitchPropertyData P where
  hereditary := D.hereditary
  trivial := by
    let f : PUnit →* FreeGroup Empty := 1
    exact D.hereditary f (fun _ _ _ ↦ Subsingleton.elim _ _) (D.free Empty)
  forbidden := D.forbidden
  forbidden_not := D.forbidden_not

/-- An arbitrary semantic finitely presented negative seed can be converted
to the exact syntactic datum consumed by the compiler.  The chosen code is
fixed thereafter; no effective coding of semantic types is claimed. -/
noncomputable def SwitchPropertyData.ofFinitelyPresentedSeed
    {H : Type} [Group H] [Group.IsFinitelyPresented H]
    (hereditary : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (trivial : P PUnit) (hH : ¬ P H) : SwitchPropertyData P := by
  classical
  let seed := Classical.choose (exists_code_mulEquiv H)
  let e := Classical.choice (Classical.choose_spec (exists_code_mulEquiv H))
  exact
    { hereditary := hereditary
      trivial := trivial
      forbidden := seed
      forbidden_not := fun hseed ↦
        hH (hereditary e.symm.toMonoidHom e.symm.injective hseed) }

/-- Complete second-level consequences for an arbitrary semantic finitely
presented negative seed. -/
theorem finitelyPresentedSeed_switch_package
    {H : Type} [Group H] [Group.IsFinitelyPresented H]
    (hereditary : ∀ {A B : Type} [Group A] [Group B] (f : A →* B),
      Function.Injective f → P B → P A)
    (trivial : P PUnit) (hH : ¬ P H) :
    let D := SwitchPropertyData.ofFinitelyPresentedSeed hereditary trivial hH
    Pi02Complete (RestrictedProperty D) ∧
      Sigma02Complete (RestrictedComplement D) ∧
      Pi02Hard (EnumeratedCodeProperty P) ∧
      Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) := by
  exact switch_completeness_package _

/-! ## Conditional finite-output implication -/

/-- An explicit compiler into the repository's *finite*-presentation syntax.

No inhabitant is constructed here.  In particular, the recursive event-ray
compiler above does not inhabit this structure. -/
structure FinitePresentationSwitchCompiler
    (P : (H : Type) → [Group H] → Prop) where
  compile : Code → PresentationCode
  computable_compile : Computable compile
  correct : ∀ c, AdianRabinGeneral.codeProperty P (compile c) ↔
    InfiniteDomain c

/-- The family cut out by a supplied finite-output compiler. -/
def FiniteOutputRestricted
    (C : FinitePresentationSwitchCompiler P) (c : Code) : Prop :=
  AdianRabinGeneral.codeProperty P (C.compile c)

/-- The complementary property on the very same finite-output compiler
family.  Keeping the compiler fixed is essential: the `Σ⁰₂` classification
is obtained by complementing the `Π⁰₂` truth table, not by constructing a
second compiler. -/
def FiniteOutputRestrictedComplement
    (C : FinitePresentationSwitchCompiler P) (c : Code) : Prop :=
  ¬ FiniteOutputRestricted C c

/-- Any supplied exact finite-output compiler makes its restricted family
`Π⁰₂`-complete. -/
theorem finiteOutputRestricted_pi02Complete
    (C : FinitePresentationSwitchCompiler P) :
    Pi02Complete (FiniteOutputRestricted C) := by
  constructor
  · exact (pi02_congr C.correct).2 infiniteDomain_pi02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
    exact ⟨f, hf, fun n ↦
      (hcorrect n).trans (C.correct (f n)).symm⟩

/-- The complementary restricted family is `Σ⁰₂`-complete, using the
same finite-output compiler and no additional correctness obligation. -/
theorem finiteOutputRestrictedComplement_sigma02Complete
    (C : FinitePresentationSwitchCompiler P) :
    Sigma02Complete (FiniteOutputRestrictedComplement C) :=
  pi02Complete_compl (finiteOutputRestricted_pi02Complete C)

/-- Conditional global `Π⁰₂`-hardness on finite-presentation codes. -/
theorem finiteCodeProperty_pi02Hard_of_compiler
    (C : FinitePresentationSwitchCompiler P) :
    Pi02Hard (AdianRabinGeneral.codeProperty P) := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  exact ⟨fun n ↦ C.compile (f n), C.computable_compile.comp hf,
    fun n ↦ (hcorrect n).trans (C.correct (f n)).symm⟩

/-- Conditional global `Σ⁰₂`-hardness of the complementary property
on finite-presentation codes. -/
theorem finiteCodeProperty_compl_sigma02Hard_of_compiler
    (C : FinitePresentationSwitchCompiler P) :
    Sigma02Hard (fun c ↦ ¬ AdianRabinGeneral.codeProperty P c) :=
  pi02Hard_compl (finiteCodeProperty_pi02Hard_of_compiler C)

/-- **The global second-level Rice classification supplied by a finite-output
compiler and a property-specific upper bound.**  The compiler supplies the
`Pi02` hardness of the property on all finite-presentation codes.  Once an
independent checker places that global predicate in `Pi02`, it is complete;
complementation then gives the exact `Sigma02` classification of failure with
no second compiler and no second upper-bound proof.

This is the interface between a group-theoretic finite-output compiler and a
property-specific finite-certificate theorem.  It is deliberately more precise
than the unrestricted hereditary-property slogan: heredity alone constructs no
finite-output compiler, and the upper bound is an explicit hypothesis. -/
theorem finiteCodeProperty_secondLevelComplete_of_compiler
    (C : FinitePresentationSwitchCompiler P)
    (hupper : Pi02 (AdianRabinGeneral.codeProperty P)) :
    Pi02Complete (AdianRabinGeneral.codeProperty P) ∧
      Sigma02Complete (fun c ↦ ¬ AdianRabinGeneral.codeProperty P c) := by
  have hcomplete : Pi02Complete (AdianRabinGeneral.codeProperty P) :=
    ⟨hupper, finiteCodeProperty_pi02Hard_of_compiler C⟩
  exact ⟨hcomplete, pi02Complete_compl hcomplete⟩

/-- **The complete finite-output Rice package.**  One compiler with the exact
`INF` truth table supplies both restricted completeness results and both global
hardness results.  In particular the complement never carries an independent
compiler debt. -/
theorem finiteOutput_switch_completeness_package
    (C : FinitePresentationSwitchCompiler P) :
    Pi02Complete (FiniteOutputRestricted C) ∧
      Sigma02Complete (FiniteOutputRestrictedComplement C) ∧
      Pi02Hard (AdianRabinGeneral.codeProperty P) ∧
      Sigma02Hard (fun c ↦ ¬ AdianRabinGeneral.codeProperty P c) :=
  ⟨finiteOutputRestricted_pi02Complete C,
    finiteOutputRestrictedComplement_sigma02Complete C,
    finiteCodeProperty_pi02Hard_of_compiler C,
    finiteCodeProperty_compl_sigma02Hard_of_compiler C⟩

/-! ## Operator-MF specialization -/

/-- Operator-MF viewed as a group property. -/
abbrev OperatorMFProperty : (H : Type) → [Group H] → Prop :=
  fun H _ ↦ IsOperatorMF H

/-- The general Markov datum specializes the switch to actual Operator-MF. -/
noncomputable def operatorMFSwitchData :
    SwitchPropertyData OperatorMFProperty :=
  SwitchPropertyData.ofMarkovData
    OperatorMFMarkovData.operatorMFMarkovData

/-- Operator-MF on the resulting arbitrary-seed switch family. -/
abbrev OperatorMFSwitch : Code → Prop :=
  RestrictedProperty operatorMFSwitchData

/-- Non-Operator-MF on that family. -/
abbrev NonOperatorMFSwitch : Code → Prop :=
  RestrictedComplement operatorMFSwitchData

theorem operatorMFSwitch_pi02Complete : Pi02Complete OperatorMFSwitch :=
  restrictedProperty_pi02Complete operatorMFSwitchData

theorem nonOperatorMFSwitch_sigma02Complete :
    Sigma02Complete NonOperatorMFSwitch :=
  restrictedComplement_sigma02Complete operatorMFSwitchData

theorem operatorMFEnumeratedCode_pi02Hard :
    Pi02Hard (EnumeratedCodeProperty OperatorMFProperty) :=
  enumeratedCodeProperty_pi02Hard operatorMFSwitchData

theorem nonOperatorMFEnumeratedCode_sigma02Hard :
    Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty OperatorMFProperty c) :=
  enumeratedCodeProperty_compl_sigma02Hard operatorMFSwitchData

/-- Any finitely presented non-Operator-MF group can serve as the finite
branch of an Operator-MF-complete recursive switch family. -/
noncomputable def operatorMFSwitchDataOfFinitelyPresentedNonMF
    (H : Type) [Group H] [Group.IsFinitelyPresented H]
    (hH : ¬ IsOperatorMF H) : SwitchPropertyData OperatorMFProperty :=
  SwitchPropertyData.ofFinitelyPresentedSeed
    (fun f hf hK ↦ hK.comap f hf)
    operatorMFSwitchData.trivial hH

/-- Exact completeness package for an arbitrary finitely presented
non-Operator-MF seed. -/
theorem operatorMF_finitelyPresentedNonMFSeed_package
    (H : Type) [Group H] [Group.IsFinitelyPresented H]
    (hH : ¬ IsOperatorMF H) :
    let D := operatorMFSwitchDataOfFinitelyPresentedNonMF H hH
    Pi02Complete (RestrictedProperty D) ∧
      Sigma02Complete (RestrictedComplement D) ∧
      Pi02Hard (EnumeratedCodeProperty OperatorMFProperty) ∧
      Sigma02Hard
        (fun c ↦ ¬ EnumeratedCodeProperty OperatorMFProperty c) := by
  exact switch_completeness_package _

end

end HereditaryPropertySwitchCompleteness
end GroupApproximation
