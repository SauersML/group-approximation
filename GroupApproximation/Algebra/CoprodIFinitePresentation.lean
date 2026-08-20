import GroupApproximation.Algebra.CoprodIPresentation
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# A free product of finitely many finitely presented groups is finitely presented

Mathlib has the binary case as an instance on `Monoid.Coprod`; it does not have
the indexed case, and the indexed case is what the amalgam and benign-subgroup
permanence lemmas of the Higman-embedding roadmap consume
(`notes/HIGMAN_EMBEDDING_FORMALIZATION_PLAN.md`, §6 step 1).

The proof is the payoff of `Algebra.CoprodIPresentation`: write each factor as
`PresentedGroup (s i)` with `s i` finite on finitely many generators, transport
the free product along that family of isomorphisms, and read the result as a
presented group on `Σ i, Fin (n i)` --- a finite generating type --- against
`⋃ i, (blockInj i)_* (s i)`, a finite union of finite sets.  Mathlib's instance
`Group.IsFinitelyPresented (PresentedGroup s)` for a finite `s` on a finite
generating type then finishes it.

Note which finiteness is used where: `Finite ι` is needed twice, once for the
generating type `Σ i, Fin (n i)` and once for the relator set, and nowhere
else.  Everything before the last step works for an arbitrary index type.
-/

namespace GroupApproximation
namespace CoprodIFinitePresentation

open Monoid

universe u v

/-! ## 1.  Transport along a family of isomorphisms of the factors -/

variable {ι : Type u} {G : ι → Type v} {H : ι → Type v}
  [∀ i, Group (G i)] [∀ i, Group (H i)]

/-- A family of isomorphisms of the factors induces an isomorphism of the
indexed free products.  Mathlib has no `CoprodI.congr`. -/
def coprodICongr (e : ∀ i, G i ≃* H i) : CoprodI G ≃* CoprodI H :=
  MonoidHom.toMulEquiv
    (CoprodI.lift fun i ↦ (CoprodI.of (i := i)).comp (e i).toMonoidHom)
    (CoprodI.lift fun i ↦ (CoprodI.of (i := i)).comp (e i).symm.toMonoidHom)
    (CoprodI.ext_hom _ _ fun _ ↦ MonoidHom.ext fun _ ↦ by simp)
    (CoprodI.ext_hom _ _ fun _ ↦ MonoidHom.ext fun _ ↦ by simp)

@[simp]
theorem coprodICongr_of (e : ∀ i, G i ≃* H i) (i : ι) (g : G i) :
    coprodICongr e (CoprodI.of g) = CoprodI.of (e i g) := by
  simp [coprodICongr]

/-! ## 2.  The permanence theorem -/

/-- **A free product of finitely many finitely presented groups is finitely
presented.**  The indexed form of Mathlib's instance for `Monoid.Coprod`. -/
theorem isFinitelyPresented_coprodI {ι : Type} [Finite ι] (G : ι → Type)
    [∀ i, Group (G i)] [∀ i, Group.IsFinitelyPresented (G i)] :
    Group.IsFinitelyPresented (CoprodI G) := by
  classical
  choose n s hsfin hne using fun i ↦
    Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := G i)
  -- `choose` destructures an existential; `Nonempty` needs its own witness
  have e : ∀ i, G i ≃* PresentedGroup (s i) := fun i ↦ (hne i).some
  have hrels : (CoprodIPresentation.coprodRels s).Finite := by
    unfold CoprodIPresentation.coprodRels
    exact Set.finite_iUnion fun i ↦ (hsfin i).image _
  haveI : Finite (CoprodIPresentation.coprodRels s) := hrels.to_subtype
  exact Group.IsFinitelyPresented.equiv
    ((CoprodIPresentation.coprodIPresentation s).trans (coprodICongr e).symm)

/-- The same statement as an instance, for a finite index type. -/
instance instCoprodI {ι : Type} [Finite ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Group.IsFinitelyPresented (G i)] :
    Group.IsFinitelyPresented (CoprodI G) :=
  isFinitelyPresented_coprodI G

end CoprodIFinitePresentation
end GroupApproximation
