import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.CoprodI
import Mathlib.SetTheory.Cardinal.Free

/-!
# A countable group containing every finitely presented group

There are countably many finite group presentations.  We encode one by a
natural number `n` of generators and a finite set of words in `FreeGroup
(Fin n)`, then take the indexed free product of all the presented groups.
The inclusion of each free factor is injective, so the resulting countable
group contains every finitely presented group.

This is the literal Lean version of the group denoted `U_fp` in the
MF-black-hole construction.  No enumeration or choice of representatives of
isomorphism classes is needed: repeated presentations are harmless.
-/

namespace GroupApproximation.Monsters

/-- A finite group presentation: finitely many generators and finitely many
relators in the corresponding free group. -/
abbrev FinitePresentationCode :=
  Σ n : ℕ, Finset (FreeGroup (Fin n))

instance finitePresentationCode_countable : Countable FinitePresentationCode :=
  inferInstance

/-- The group presented by a finite-presentation code. -/
abbrev CodedPresentedGroup (c : FinitePresentationCode) : Type :=
  PresentedGroup (c.2 : Set (FreeGroup (Fin c.1)))

instance codedPresentedGroup_group (c : FinitePresentationCode) :
    Group (CodedPresentedGroup c) :=
  inferInstance

instance codedPresentedGroup_countable (c : FinitePresentationCode) :
    Countable (CodedPresentedGroup c) := by
  change Countable
    (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure (c.2 : Set (FreeGroup (Fin c.1))))))
  infer_instance

/-- The indexed free product of all finitely presented groups, with one free
factor for every finite presentation. -/
abbrev UniversalFinitelyPresentedGroup : Type :=
  Monoid.CoprodI CodedPresentedGroup

instance universalFinitelyPresentedGroup_countable :
    Countable UniversalFinitelyPresentedGroup := by
  change Countable
    (Quotient (conGen (Monoid.CoprodI.Rel CodedPresentedGroup)).toSetoid)
  infer_instance

/-- Every finitely presented group is isomorphic to the group attached to one
of the concrete finite-presentation codes. -/
theorem exists_mulEquiv_codedPresentedGroup
    (G : Type) [Group G] [Group.IsFinitelyPresented G] :
    ∃ c : FinitePresentationCode, Nonempty (G ≃* CodedPresentedGroup c) := by
  classical
  obtain ⟨n, rels, hrels, ⟨e⟩⟩ :=
    Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G)
  let c : FinitePresentationCode := ⟨n, hrels.toFinset⟩
  refine ⟨c, ⟨?_⟩⟩
  change G ≃* PresentedGroup (hrels.toFinset : Set (FreeGroup (Fin n)))
  rw [hrels.coe_toFinset]
  exact e

/-- Every finitely presented group embeds into the universal indexed free
product. -/
theorem embeds_universalFinitelyPresentedGroup
    (G : Type) [Group G] [Group.IsFinitelyPresented G] :
    ∃ f : G →* UniversalFinitelyPresentedGroup,
      Function.Injective f := by
  classical
  obtain ⟨c, ⟨e'⟩⟩ := exists_mulEquiv_codedPresentedGroup G
  let f : G →* UniversalFinitelyPresentedGroup :=
    (Monoid.CoprodI.of (i := c)).comp e'.toMonoidHom
  refine ⟨f, ?_⟩
  exact (Monoid.CoprodI.of_injective c).comp e'.injective

/-- In particular, every finite group embeds into the universal group. -/
theorem embeds_universalFinitelyPresentedGroup_of_finite
    (F : Type) [Group F] [Finite F] :
    ∃ f : F →* UniversalFinitelyPresentedGroup,
      Function.Injective f :=
  embeds_universalFinitelyPresentedGroup F

/-- The universal finitely presented subgroup is infinite; it already
contains the infinite cyclic group. -/
instance universalFinitelyPresentedGroup_infinite :
    Infinite UniversalFinitelyPresentedGroup := by
  obtain ⟨f, hf⟩ :=
    embeds_universalFinitelyPresentedGroup (Multiplicative ℤ)
  exact Infinite.of_injective f hf

end GroupApproximation.Monsters
