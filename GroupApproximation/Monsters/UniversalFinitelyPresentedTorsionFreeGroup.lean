import GroupApproximation.Monsters.UniversalFinitelyPresentedGroup
import GroupApproximation.Monsters.VerbalCompleteness
import GroupApproximation.Algebra.GroupTorsionFree
import Mathlib.Data.DFinsupp.Encodable
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# A countable torsion-free universal subgroup payload

We retain precisely those finite presentation codes whose presented groups
are torsion-free, and put all of them into a restricted direct product.  The
restricted product is implemented as a multiplicative copy of a dependent
finitely-supported function type.  It is countable, torsion-free, and every
finitely presented torsion-free group embeds as one coordinate.

Taking its direct product with `ℤ` supplies a distinguished nontrivial central
element.  This is the payload transported into every nonidentity centralizer
in the Hitchhiker construction.
-/

namespace GroupApproximation.Monsters

/-- Finite presentations whose presented group is torsion-free. -/
def TorsionFreePresentationCode :=
  {c : FinitePresentationCode // IsPowerTorsionFree (CodedPresentedGroup c)}

instance torsionFreePresentationCode_countable :
    Countable TorsionFreePresentationCode :=
  by
    unfold TorsionFreePresentationCode
    exact Subtype.countable

/-- The group attached to a torsion-free presentation code. -/
abbrev TorsionFreeCodedGroup (c : TorsionFreePresentationCode) : Type :=
  CodedPresentedGroup c.1

instance torsionFreeCodedGroup_group (c : TorsionFreePresentationCode) :
    Group (TorsionFreeCodedGroup c) := inferInstance

theorem torsionFreeCodedGroup_torsionFree (c : TorsionFreePresentationCode) :
    IsPowerTorsionFree (TorsionFreeCodedGroup c) := c.2

instance torsionFreeCodedGroup_countable (c : TorsionFreePresentationCode) :
    Countable (TorsionFreeCodedGroup c) := inferInstance

instance torsionFreeCodedGroup_additive_countable
    (c : TorsionFreePresentationCode) :
    Countable (Additive (TorsionFreeCodedGroup c)) :=
  Countable.of_equiv (TorsionFreeCodedGroup c) Additive.ofMul

/-- The restricted direct product of all finitely presented torsion-free
groups.  `DFinsupp` makes the support finite, hence preserves countability. -/
def UniversalFinitelyPresentedTorsionFreeGroup : Type :=
  Multiplicative
    (Π₀ c : TorsionFreePresentationCode, Additive (TorsionFreeCodedGroup c))

instance universalFinitelyPresentedTorsionFreeGroup_group :
    Group UniversalFinitelyPresentedTorsionFreeGroup := by
  unfold UniversalFinitelyPresentedTorsionFreeGroup
  infer_instance

instance universalFinitelyPresentedTorsionFreeGroup_countable :
    Countable UniversalFinitelyPresentedTorsionFreeGroup :=
  by
    unfold UniversalFinitelyPresentedTorsionFreeGroup
    exact Countable.of_equiv
      (Π₀ c : TorsionFreePresentationCode, Additive (TorsionFreeCodedGroup c))
      Multiplicative.ofAdd

/-- Inclusion of one coordinate into the restricted direct product. -/
noncomputable def restrictedDirectProductOf (c : TorsionFreePresentationCode) :
    TorsionFreeCodedGroup c →* UniversalFinitelyPresentedTorsionFreeGroup := by
  classical
  exact
    { toFun := fun x ↦
        Multiplicative.ofAdd (DFinsupp.single c (Additive.ofMul x))
      map_one' := by
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (1 : TorsionFreeCodedGroup c))) =
          Multiplicative.ofAdd
            (0 : (Π₀ i : TorsionFreePresentationCode,
              Additive (TorsionFreeCodedGroup i)))
        apply Multiplicative.ofAdd.injective
        simp
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (x * y))) =
          Multiplicative.ofAdd
            ((DFinsupp.single c (Additive.ofMul x) :
                (Π₀ i : TorsionFreePresentationCode,
                  Additive (TorsionFreeCodedGroup i))) +
              (DFinsupp.single c (Additive.ofMul y) :
                (Π₀ i : TorsionFreePresentationCode,
                  Additive (TorsionFreeCodedGroup i))))
        exact congrArg Multiplicative.ofAdd
          ((DFinsupp.single_add
            (β := fun i : TorsionFreePresentationCode ↦
              Additive (TorsionFreeCodedGroup i)) c (Additive.ofMul x)
            (Additive.ofMul y))) }

/-- Evaluation at one presentation coordinate. -/
noncomputable def restrictedDirectProductEval
    (c : TorsionFreePresentationCode) :
    UniversalFinitelyPresentedTorsionFreeGroup →* TorsionFreeCodedGroup c where
  toFun q := Additive.toMul (Multiplicative.toAdd q c)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A coordinate inclusion is injective. -/
theorem restrictedDirectProductOf_injective (c : TorsionFreePresentationCode) :
    Function.Injective (restrictedDirectProductOf c) := by
  intro x y hxy
  have h := congrArg
    (fun q : UniversalFinitelyPresentedTorsionFreeGroup ↦
      Additive.toMul (Multiplicative.toAdd q c)) hxy
  simpa [restrictedDirectProductOf] using h

/-- The restricted direct product is torsion-free because powers are tested
coordinatewise. -/
theorem universalFinitelyPresentedTorsionFreeGroup_torsionFree :
    IsPowerTorsionFree UniversalFinitelyPresentedTorsionFreeGroup := by
  intro g n hn hpow
  apply Multiplicative.toAdd.injective
  apply DFinsupp.ext
  intro c
  apply Additive.toMul.injective
  apply c.2 (Additive.toMul (Multiplicative.toAdd g c)) n hn
  change (restrictedDirectProductEval c g) ^ n = 1
  simpa using congrArg (restrictedDirectProductEval c) hpow

/-- Every finitely presented torsion-free group embeds into the restricted
direct product. -/
theorem embeds_universalFinitelyPresentedTorsionFreeGroup
    (G : Type) [Group G] [Group.IsFinitelyPresented G]
    (hG : IsPowerTorsionFree G) :
    ∃ f : G →* UniversalFinitelyPresentedTorsionFreeGroup,
      Function.Injective f := by
  classical
  obtain ⟨c, ⟨e'⟩⟩ := exists_mulEquiv_codedPresentedGroup G
  let htf : IsPowerTorsionFree (CodedPresentedGroup c) := by
    intro g n hn hpow
    apply e'.symm.injective
    simpa using hG (e'.symm g) n hn (by
      simpa using congrArg e'.symm hpow)
  let tc : TorsionFreePresentationCode := ⟨c, htf⟩
  let f : G →* UniversalFinitelyPresentedTorsionFreeGroup :=
    (restrictedDirectProductOf tc).comp e'.toMonoidHom
  exact ⟨f, (restrictedDirectProductOf_injective tc).comp e'.injective⟩

/-- The payload placed in a centralizer: the universal torsion-free group
together with one explicit infinite cyclic central coordinate. -/
abbrev UniversalCentralizerPayload : Type :=
  UniversalFinitelyPresentedTorsionFreeGroup × Multiplicative ℤ

instance universalCentralizerPayload_countable :
    Countable UniversalCentralizerPayload := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  infer_instance

theorem universalCentralizerPayload_torsionFree :
    IsPowerTorsionFree UniversalCentralizerPayload :=
  IsPowerTorsionFree.prod
    universalFinitelyPresentedTorsionFreeGroup_torsionFree
    IsPowerTorsionFree.of_isMulTorsionFree

/-- The fixed nonidentity central element of the payload. -/
def universalCentralizerElement : UniversalCentralizerPayload :=
  (1, Multiplicative.ofAdd 1)

theorem universalCentralizerElement_ne_one :
    universalCentralizerElement ≠ 1 := by
  intro h
  have := congrArg (fun x : UniversalCentralizerPayload ↦
    Multiplicative.toAdd x.2) h
  change (1 : ℤ) = 0 at this
  exact one_ne_zero this

theorem universalCentralizerElement_mem_center :
    universalCentralizerElement ∈ Subgroup.center UniversalCentralizerPayload := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Prod.ext
  · simp [universalCentralizerElement]
  · change x.2 * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 1 * x.2
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd x.2 + (1 : ℤ) = 1 + Multiplicative.toAdd x.2
    exact add_comm _ _

/-- Every finitely presented torsion-free group embeds in the centralizer
payload. -/
theorem embeds_universalCentralizerPayload
    (G : Type) [Group G] [Group.IsFinitelyPresented G]
    (hG : IsPowerTorsionFree G) :
    ∃ f : G →* UniversalCentralizerPayload, Function.Injective f := by
  obtain ⟨e, he⟩ := embeds_universalFinitelyPresentedTorsionFreeGroup G hG
  let f : G →* UniversalCentralizerPayload :=
    { toFun := fun g ↦ (e g, 1)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  exact ⟨f, fun x y h ↦ he (congrArg Prod.fst h)⟩

/-- In particular the payload contains a free group of every finite rank. -/
theorem embeds_freeGroup_universalCentralizerPayload (m : ℕ) :
    ∃ f : FreeGroup (Fin m) →* UniversalCentralizerPayload,
      Function.Injective f :=
  embeds_universalCentralizerPayload (FreeGroup (Fin m))
    IsPowerTorsionFree.of_isMulTorsionFree

/-- The centralizer payload contains free groups of every finite rank. -/
theorem universalCentralizerPayload_containsEveryFiniteRankFreeGroup :
    ContainsEveryFiniteRankFreeGroup UniversalCentralizerPayload :=
  embeds_freeGroup_universalCentralizerPayload

/-- The unconditional package supplied by the explicit restricted-product
construction.  It needs no ambient group and no proof-carrying construction
data. -/
theorem universalCentralizerPayload_package :
    Countable UniversalCentralizerPayload ∧
      IsPowerTorsionFree UniversalCentralizerPayload ∧
      universalCentralizerElement ≠ 1 ∧
      universalCentralizerElement ∈
        Subgroup.center UniversalCentralizerPayload ∧
      ContainsEveryFiniteRankFreeGroup UniversalCentralizerPayload ∧
      (∀ (G : Type) [Group G] [Group.IsFinitelyPresented G]
        (_hG : IsPowerTorsionFree G),
        ∃ f : G →* UniversalCentralizerPayload, Function.Injective f) := by
  exact ⟨inferInstance, universalCentralizerPayload_torsionFree,
    universalCentralizerElement_ne_one,
    universalCentralizerElement_mem_center,
    universalCentralizerPayload_containsEveryFiniteRankFreeGroup,
    fun G _ _ hG ↦ embeds_universalCentralizerPayload G hG⟩

/-- Once the payload is embedded in a two-conjugacy-class group, every
nonidentity centralizer contains every finitely presented torsion-free group. -/
theorem every_finitelyPresented_torsionFree_group_embeds_centralizer
    {G : Type*} [Group G] (hcc : HasTwoConjugacyClasses G)
    (payload : UniversalCentralizerPayload →* G)
    (hpayload : Function.Injective payload)
    {g : G} (hg : g ≠ 1)
    (H : Type) [Group H] [Group.IsFinitelyPresented H]
    (hH : IsPowerTorsionFree H) :
    ∃ f : H →* Subgroup.centralizer ({g} : Set G), Function.Injective f := by
  obtain ⟨j, hj⟩ := hcc.embeds_into_centralizer payload hpayload
    universalCentralizerElement_mem_center
    universalCentralizerElement_ne_one hg
  obtain ⟨e, he⟩ := embeds_universalCentralizerPayload H hH
  exact ⟨j.comp e, hj.comp he⟩

end GroupApproximation.Monsters
