import GroupApproximation.Sofic.LiteralFiniteDimensionalObstruction
import GroupApproximation.Meta.AxiomGuard

/-!
# `E` is a group of Deligne type

Manuscript `non_mf_group_notes.tex`, opening paragraph of `sec:findim`
(tex 987--998):

> The central involution `w` lies in the kernel of every homomorphism to a
> finite group, so `E` is a group of *Deligne type* in the terminology of
> [BDL, Definition 1.2].

[BDL, Definition 1.2] calls a group of Deligne type if it is finitely
generated and has a central element of order two lying in every finite-index
normal subgroup.  `IsDeligneTypeBDL` states this definition in the same shape
as the (foreign, unwired) `RelatedBDL.Definitions.IsDeligneType`; it is
re-stated locally so that this lane does not import that directory.

The instance for the literal eight-generator group
`LiteralNonMFPresentation.MarkedGroup` (the printed `E`) is assembled from
rooted declarations:

* `LiteralNonMFPresentation.mark_central`, `LiteralNonMFPresentation.mark_sq`;
* `LiteralNonMFLinearWitness.literal_mark_ne_one` (the Clifford witness);
* `LiteralFiniteDimensionalObstruction.map_literal_mark_eq_one_of_finite`.
-/

namespace GroupApproximation.Full.NN12

/-- **Groups of Deligne type** ([BDL, Definition 1.2]): `Γ` is finitely
generated and has a central element `J` of order two that is killed by every
homomorphism to a finite group. -/
def IsDeligneTypeBDL (Γ : Type) [Group Γ] : Prop :=
  Group.FG Γ ∧ ∃ J : Γ, orderOf J = 2 ∧ (∀ g : Γ, g * J = J * g) ∧
    ∀ (F : Type) [Group F] [Finite F] (f : Γ →* F), f J = 1

/-- The literal group `E` is finitely generated: it is a quotient of the free
group on the eight letters. -/
theorem markedGroup_fg : Group.FG LiteralNonMFPresentation.MarkedGroup :=
  Group.fg_of_surjective (PresentedGroup.mk_surjective _)

/-- The central involution `w` of `E` has order exactly two. -/
theorem orderOf_mark : orderOf LiteralNonMFPresentation.mark = 2 :=
  orderOf_eq_prime LiteralNonMFPresentation.mark_sq
    LiteralNonMFLinearWitness.literal_mark_ne_one

/-- **`E` is a group of Deligne type** (`sec:findim`, tex 994--996). -/
theorem markedGroup_isDeligneType :
    IsDeligneTypeBDL LiteralNonMFPresentation.MarkedGroup :=
  ⟨markedGroup_fg, LiteralNonMFPresentation.mark, orderOf_mark,
    fun g => (LiteralNonMFPresentation.mark_central g).eq.symm,
    fun _ _ _ f => LiteralFiniteDimensionalObstruction.map_literal_mark_eq_one_of_finite f⟩

/-- **The printed paragraph of `sec:findim`** as one conjunction: `E` is
finitely presented, no finite-dimensional linear representation over a field
is faithful, the central involution is nontrivial, and `E` is of Deligne
type. -/
theorem findim_paragraph_printed :
    Group.IsFinitelyPresented LiteralNonMFPresentation.MarkedGroup ∧
      (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
          (π : LiteralNonMFPresentation.MarkedGroup →* (Module.End k V)ˣ),
          ¬ Function.Injective π) ∧
      LiteralNonMFPresentation.mark ≠ 1 ∧
      IsDeligneTypeBDL LiteralNonMFPresentation.MarkedGroup :=
  ⟨LiteralNonMFPresentation.markedGroup_finitelyPresented,
    fun _ _ _ _ _ _ π =>
      LiteralFiniteDimensionalObstruction.literal_finiteDimensional_rep_not_injective π,
    LiteralNonMFLinearWitness.literal_mark_ne_one, markedGroup_isDeligneType⟩

#audit_axioms markedGroup_fg
#audit_axioms orderOf_mark
#audit_axioms markedGroup_isDeligneType
#audit_axioms findim_paragraph_printed

end GroupApproximation.Full.NN12
