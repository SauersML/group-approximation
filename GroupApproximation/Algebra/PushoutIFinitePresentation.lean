import GroupApproximation.Algebra.CoprodIFinitePresentation
import Mathlib.GroupTheory.PushoutI

/-!
# An amalgamated free product of finitely presented groups is finitely presented

Provided the index type is finite and nonempty and the amalgamated group is
finitely generated.  Mathlib has neither this statement nor any part of it, and
`Algebra.HNNFinitePresentation` is its exact analogue for HNN extensions --- the
two together are the permanence half of the benign-subgroup calculus of the
Higman-embedding roadmap (`notes/HIGMAN_EMBEDDING_FORMALIZATION_PLAN.md`, §6
step 1).

## The shape of the argument

It is `Algebra.HNNFinitePresentation` with the stable letter replaced by a
second factor.  `Monoid.PushoutI φ` is the free product `⨿ᵢ Gᵢ` modulo the
relations `ιᵢ(φᵢ h) = ιⱼ(φⱼ h)`, one for every `h : H`; pinning a base index
`i₀`, it is enough to impose

    relator i h  :  of i (φ i h) · (of i₀ (φ i₀ h))⁻¹

and the content of the file is that the *infinite* family `{relator i h : h : H}`
may be replaced by the finitely many relators coming from a generating set of
`H`.  That replacement is the one place finite generation of `H` is used, and it
is the same equalizer argument as in the HNN file: `h ↦ qOf i (φ i h)` and
`h ↦ qOf i₀ (φ i₀ h)` are both homomorphisms `H →* Q`, so they agree on all of
`H` as soon as they agree on a generating set (`MonoidHom.eq_of_eqOn_dense`).

The ambient group is finitely presented by
`CoprodIFinitePresentation.isFinitelyPresented_coprodI`, which is where the
finiteness of the index type is used the second time.

No injectivity of the `φ i` is needed anywhere; this is a statement about the
pushout, not about the amalgam, and it specializes to the amalgam.
-/

namespace GroupApproximation
namespace PushoutIFinitePresentation

open Monoid

variable {ι : Type} {G : ι → Type} {H : Type} [∀ i, Group (G i)] [Group H]
  (φ : ∀ i, H →* G i) (i₀ : ι)

/-! ## 1.  The relators -/

/-- The relator identifying the image of `h` in the `i`-th factor with its
image in the base factor `i₀`. -/
def relator (i : ι) (h : H) : CoprodI G :=
  CoprodI.of (φ i h) * (CoprodI.of (φ i₀ h))⁻¹

/-- The relators coming from a set of elements of the amalgamated group. -/
def relators (S : Set H) : Set (CoprodI G) :=
  (fun p : ι × H ↦ relator φ i₀ p.1 p.2) '' (Set.univ ×ˢ S)

theorem mem_relators {S : Set H} {i : ι} {h : H} (hh : h ∈ S) :
    relator φ i₀ i h ∈ relators φ i₀ S :=
  ⟨(i, h), ⟨Set.mem_univ i, hh⟩, rfl⟩

theorem relators_finite [Finite ι] {S : Set H} (hS : S.Finite) :
    (relators φ i₀ S).Finite :=
  (Set.finite_univ.prod hS).image _

/-! ## 2.  The canonical map onto the pushout -/

/-- Every relator dies in the pushout: that is the defining relation. -/
theorem ofCoprodI_relator (i : ι) (h : H) :
    (PushoutI.ofCoprodI (relator φ i₀ i h) : PushoutI φ) = 1 := by
  simp only [relator, map_mul, map_inv, PushoutI.ofCoprodI_of]
  rw [PushoutI.of_apply_eq_base φ i h, PushoutI.of_apply_eq_base φ i₀ h,
    mul_inv_cancel]

theorem normalClosure_relators_le_ker (S : Set H) :
    Subgroup.normalClosure (relators φ i₀ S) ≤
      (PushoutI.ofCoprodI (φ := φ)).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨⟨i, h⟩, -, rfl⟩
  exact ofCoprodI_relator φ i₀ i h

/-! ## 3.  The quotient by the finitely many relators -/

section Quotient

variable (S : Set H)

/-- The normal closure of the relators of `S` inside the free product. -/
abbrev Rel : Subgroup (CoprodI G) := Subgroup.normalClosure (relators φ i₀ S)

/-- The candidate presentation of the pushout. -/
abbrev Q : Type := CoprodI G ⧸ Rel φ i₀ S

/-- The image of the `i`-th factor in the quotient. -/
def qOf (i : ι) : G i →* Q φ i₀ S :=
  (QuotientGroup.mk' (Rel φ i₀ S)).comp (CoprodI.of (i := i))

variable {S}

/-- The defining relation, in the quotient, for a generator of `H`. -/
theorem relation_of_mem {i : ι} {h : H} (hh : h ∈ S) :
    qOf φ i₀ S i (φ i h) = qOf φ i₀ S i₀ (φ i₀ h) := by
  have hmem : relator φ i₀ i h ∈ Rel φ i₀ S :=
    Subgroup.subset_normalClosure (mem_relators φ i₀ hh)
  have h1 : QuotientGroup.mk' (Rel φ i₀ S) (relator φ i₀ i h) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hmem
  simp only [relator, map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- One side of the defining relation, as a homomorphism out of `H`. -/
def leftHom (i : ι) : H →* Q φ i₀ S := (qOf φ i₀ S i).comp (φ i)

/-- The other side, the base one. -/
def baseHom : H →* Q φ i₀ S := (qOf φ i₀ S i₀).comp (φ i₀)

@[simp] theorem leftHom_apply (i : ι) (h : H) :
    leftHom φ i₀ (S := S) i h = qOf φ i₀ S i (φ i h) := rfl

@[simp] theorem baseHom_apply (h : H) :
    baseHom φ i₀ (S := S) h = qOf φ i₀ S i₀ (φ i₀ h) := rfl

/-- **Where finite generation of `H` is used.**  Two homomorphisms agreeing on
a generating set agree everywhere, so the relations imposed for `S` already
impose the relation for every element of `H`. -/
theorem leftHom_eq_baseHom (hS : Subgroup.closure S = ⊤) (i : ι) :
    leftHom φ i₀ (S := S) i = baseHom φ i₀ (S := S) :=
  MonoidHom.eq_of_eqOn_dense hS fun _ hh => relation_of_mem φ i₀ hh

/-- The inverse map, out of the pushout. -/
def fromPush (hS : Subgroup.closure S = ⊤) : PushoutI φ →* Q φ i₀ S :=
  PushoutI.lift (fun i ↦ qOf φ i₀ S i) (baseHom φ i₀)
    (leftHom_eq_baseHom φ i₀ hS)

@[simp] theorem fromPush_of (hS : Subgroup.closure S = ⊤) (i : ι) (g : G i) :
    fromPush φ i₀ hS (PushoutI.of i g) = qOf φ i₀ S i g :=
  PushoutI.lift_of _ _ _ _

/-- The quotient map, factored through the relators. -/
def toPush : Q φ i₀ S →* PushoutI φ :=
  QuotientGroup.lift _ PushoutI.ofCoprodI (normalClosure_relators_le_ker φ i₀ S)

@[simp] theorem toPush_mk (x : CoprodI G) :
    toPush φ i₀ (S := S) (QuotientGroup.mk' (Rel φ i₀ S) x) =
      PushoutI.ofCoprodI x := rfl

theorem toPush_comp_fromPush [Nonempty ι] (hS : Subgroup.closure S = ⊤) :
    (toPush φ i₀ (S := S)).comp (fromPush φ i₀ hS) = MonoidHom.id _ := by
  refine PushoutI.hom_ext_nonempty ?_
  intro i
  refine MonoidHom.ext fun g ↦ ?_
  show toPush φ i₀ (S := S) (fromPush φ i₀ hS (PushoutI.of i g)) =
    PushoutI.of i g
  rw [fromPush_of]
  show PushoutI.ofCoprodI (CoprodI.of g) = PushoutI.of i g
  exact PushoutI.ofCoprodI_of i g

theorem fromPush_comp_toPush (hS : Subgroup.closure S = ⊤) :
    (fromPush φ i₀ hS).comp (toPush φ i₀ (S := S)) = MonoidHom.id _ := by
  have key : ((fromPush φ i₀ hS).comp (toPush φ i₀ (S := S))).comp
      (QuotientGroup.mk' (Rel φ i₀ S))
      = (MonoidHom.id (Q φ i₀ S)).comp (QuotientGroup.mk' (Rel φ i₀ S)) := by
    refine CoprodI.ext_hom _ _ fun i ↦ MonoidHom.ext fun g ↦ ?_
    show fromPush φ i₀ hS (PushoutI.ofCoprodI (CoprodI.of g)) =
      QuotientGroup.mk' (Rel φ i₀ S) (CoprodI.of g)
    rw [PushoutI.ofCoprodI_of, fromPush_of]
    rfl
  refine MonoidHom.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Rel φ i₀ S) q
  exact congrArg (fun f : CoprodI G →* Q φ i₀ S ↦ f x) key

/-- The candidate presentation really does present the pushout. -/
def quotientEquiv [Nonempty ι] (hS : Subgroup.closure S = ⊤) :
    Q φ i₀ S ≃* PushoutI φ where
  toFun := toPush φ i₀
  invFun := fromPush φ i₀ hS
  left_inv q :=
    congrArg (fun f : Q φ i₀ S →* Q φ i₀ S ↦ f q)
      (fromPush_comp_toPush φ i₀ hS)
  right_inv x :=
    congrArg (fun f : PushoutI φ →* PushoutI φ ↦ f x)
      (toPush_comp_fromPush φ i₀ hS)
  map_mul' := map_mul _

end Quotient

/-! ## 4.  The permanence theorem -/

/-- **A pushout of finitely many finitely presented groups along a finitely
generated group is finitely presented.**  In particular an amalgamated free
product `G₁ *_H G₂` of finitely presented groups over a finitely generated
subgroup is finitely presented. -/
theorem isFinitelyPresented_pushoutI [Finite ι] [Nonempty ι]
    [∀ i, Group.IsFinitelyPresented (G i)] [Group.FG H] :
    Group.IsFinitelyPresented (PushoutI φ) := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  obtain ⟨S, hclosure, hfinite⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  haveI : Group.IsFinitelyPresented (Q φ j S) :=
    Group.IsFinitelyPresented.quotient (Rel φ j S)
      ⟨relators φ j S, relators_finite φ j hfinite, rfl⟩
  exact Group.IsFinitelyPresented.equiv (quotientEquiv φ j hclosure)

end PushoutIFinitePresentation
end GroupApproximation
