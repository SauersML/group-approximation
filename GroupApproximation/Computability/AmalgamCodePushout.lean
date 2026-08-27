import GroupApproximation.Computability.AmalgamCodeSemantics
import GroupApproximation.Higman.AmalgamPushout

/-!
# The displayed amalgam code is a pushout

Each occurrence in the finite edge list is made a generator of a free edge
group.  The two word-evaluation homomorphisms from that free group give a
two-factor `PushoutI`.  This file identifies the semantic quotient presentation
of `AmalgamCodeSemantics` with that pushout, without injectivity assumptions.
-/

namespace GroupApproximation
namespace AmalgamCodePushout

open Monoid
open PresentationCodes PresentedGroupRelabel
open AmalgamCode AmalgamCodeSemantics RawWord

abbrev Raw : Type := AmalgamCode.Raw

abbrev EdgeLetter (edges : List (Raw × Raw)) :=
  {p : Raw × Raw // p ∈ edges}

abbrev EdgeGroup (edges : List (Raw × Raw)) := FreeGroup (EdgeLetter edges)

def leftEdgeGenerator (c : PresentationCode) {edges : List (Raw × Raw)}
    (p : EdgeLetter edges) : Carrier c :=
  PresentedGroup.mk (codeRels c) (wordOf c p.1.1)

def rightEdgeGenerator (d : PresentationCode) {edges : List (Raw × Raw)}
    (p : EdgeLetter edges) : Carrier d :=
  PresentedGroup.mk (codeRels d) (wordOf d p.1.2)

def leftEdgeHom (c : PresentationCode) (edges : List (Raw × Raw)) :
    EdgeGroup edges →* Carrier c :=
  FreeGroup.lift (leftEdgeGenerator c)

def rightEdgeHom (d : PresentationCode) (edges : List (Raw × Raw)) :
    EdgeGroup edges →* Carrier d :=
  FreeGroup.lift (rightEdgeGenerator d)

abbrev Push (c d : PresentationCode) (edges : List (Raw × Raw)) :=
  Higman.Amalgam.Push (leftEdgeHom c edges) (rightEdgeHom d edges)

def pushGenerator (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Fin (genCount c) ⊕ Fin (genCount d) → Push c d edges
  | Sum.inl i => PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      false (PresentedGroup.of i)
  | Sum.inr j => PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      true (PresentedGroup.of j)

theorem lift_pushGenerator_inl (c d : PresentationCode)
    (edges : List (Raw × Raw)) (w : FreeGroup (Fin (genCount c))) :
    FreeGroup.lift (pushGenerator c d edges) (relabel Sum.inl w) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        false (PresentedGroup.mk (codeRels c) w) := by
  refine freeGroup_hom_eq_on_generators
    (f := (FreeGroup.lift (pushGenerator c d edges)).comp (relabel Sum.inl))
    (g := (PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      false).comp (PresentedGroup.mk (codeRels c))) ?_ w
  intro i
  change PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      false (PresentedGroup.of i) = _
  rfl

theorem lift_pushGenerator_inr (c d : PresentationCode)
    (edges : List (Raw × Raw)) (w : FreeGroup (Fin (genCount d))) :
    FreeGroup.lift (pushGenerator c d edges) (relabel Sum.inr w) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        true (PresentedGroup.mk (codeRels d) w) := by
  refine freeGroup_hom_eq_on_generators
    (f := (FreeGroup.lift (pushGenerator c d edges)).comp (relabel Sum.inr))
    (g := (PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      true).comp (PresentedGroup.mk (codeRels d))) ?_ w
  intro j
  change PushoutI.of
      (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      true (PresentedGroup.of j) = _
  rfl

theorem pushGenerator_kills (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    ∀ r ∈ amalgamRels c d edges,
      FreeGroup.lift (pushGenerator c d edges) r = 1 := by
  rintro r ((hr | hr) | hr)
  · obtain ⟨r, hr, rfl⟩ := hr
    rw [lift_pushGenerator_inl]
    rw [PresentedGroup.mk_eq_one_iff.mpr
      (Subgroup.subset_normalClosure hr)]
    exact map_one _
  · obtain ⟨r, hr, rfl⟩ := hr
    rw [lift_pushGenerator_inr]
    rw [PresentedGroup.mk_eq_one_iff.mpr
      (Subgroup.subset_normalClosure hr)]
    exact map_one _
  · obtain ⟨p, hp, rfl⟩ := hr
    let q : EdgeLetter edges := ⟨p, hp⟩
    rw [edgeRelator, map_mul, map_inv, lift_pushGenerator_inl,
      lift_pushGenerator_inr]
    have hl := PushoutI.of_apply_eq_base
      (Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      false (FreeGroup.of q)
    have hr := PushoutI.of_apply_eq_base
      (Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
      true (FreeGroup.of q)
    have hl' : PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        false (PresentedGroup.mk (codeRels c) (wordOf c p.1)) =
        PushoutI.base
          (Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
          (FreeGroup.of q) := by
      have heval : leftEdgeHom c edges (FreeGroup.of q) =
          PresentedGroup.mk (codeRels c) (wordOf c p.1) := by
        change FreeGroup.lift (leftEdgeGenerator c) (FreeGroup.of q) = _
        rw [FreeGroup.lift_apply_of]
        rfl
      change PushoutI.of
          (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
          false (leftEdgeHom c edges (FreeGroup.of q)) = _ at hl
      rw [heval] at hl
      exact hl
    have hr' : PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        true (PresentedGroup.mk (codeRels d) (wordOf d p.2)) =
        PushoutI.base
          (Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
          (FreeGroup.of q) := by
      have heval : rightEdgeHom d edges (FreeGroup.of q) =
          PresentedGroup.mk (codeRels d) (wordOf d p.2) := by
        change FreeGroup.lift (rightEdgeGenerator d) (FreeGroup.of q) = _
        rw [FreeGroup.lift_apply_of]
        rfl
      change PushoutI.of
          (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
          true (rightEdgeHom d edges (FreeGroup.of q)) = _ at hr
      rw [heval] at hr
      exact hr
    rw [hl', hr', mul_inv_cancel]

def toPush (c d : PresentationCode) (edges : List (Raw × Raw)) :
    PresentedGroup (amalgamRels c d edges) →* Push c d edges :=
  PresentedGroup.toGroup (pushGenerator_kills c d edges)

def leftGenerator (c d : PresentationCode) (edges : List (Raw × Raw))
    (i : Fin (genCount c)) : PresentedGroup (amalgamRels c d edges) :=
  PresentedGroup.of (Sum.inl i)

def rightGenerator (c d : PresentationCode) (edges : List (Raw × Raw))
    (j : Fin (genCount d)) : PresentedGroup (amalgamRels c d edges) :=
  PresentedGroup.of (Sum.inr j)

theorem leftGenerator_kills (c d : PresentationCode)
    (edges : List (Raw × Raw)) : ∀ r ∈ codeRels c,
      FreeGroup.lift (leftGenerator c d edges) r = 1 := by
  intro r hr
  have hrel : relabel Sum.inl r ∈ amalgamRels c d edges :=
    Or.inl (Or.inl ⟨r, hr, rfl⟩)
  rw [show FreeGroup.lift (leftGenerator c d edges) r =
      PresentedGroup.mk (amalgamRels c d edges) (relabel Sum.inl r) by
    refine freeGroup_hom_eq_on_generators
      (f := FreeGroup.lift (leftGenerator c d edges))
      (g := (PresentedGroup.mk (amalgamRels c d edges)).comp
        (relabel Sum.inl)) ?_ r
    intro i
    simp [leftGenerator, relabel, PresentedGroup.of]]
  exact PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure hrel)

theorem rightGenerator_kills (c d : PresentationCode)
    (edges : List (Raw × Raw)) : ∀ r ∈ codeRels d,
      FreeGroup.lift (rightGenerator c d edges) r = 1 := by
  intro r hr
  have hrel : relabel Sum.inr r ∈ amalgamRels c d edges :=
    Or.inl (Or.inr ⟨r, hr, rfl⟩)
  rw [show FreeGroup.lift (rightGenerator c d edges) r =
      PresentedGroup.mk (amalgamRels c d edges) (relabel Sum.inr r) by
    refine freeGroup_hom_eq_on_generators
      (f := FreeGroup.lift (rightGenerator c d edges))
      (g := (PresentedGroup.mk (amalgamRels c d edges)).comp
        (relabel Sum.inr)) ?_ r
    intro j
    simp [rightGenerator, relabel, PresentedGroup.of]]
  exact PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure hrel)

def leftHom (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Carrier c →* PresentedGroup (amalgamRels c d edges) :=
  PresentedGroup.toGroup (leftGenerator_kills c d edges)

def rightHom (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Carrier d →* PresentedGroup (amalgamRels c d edges) :=
  PresentedGroup.toGroup (rightGenerator_kills c d edges)

theorem leftHom_mk (c d : PresentationCode) (edges : List (Raw × Raw))
    (w : FreeGroup (Fin (genCount c))) :
    leftHom c d edges (PresentedGroup.mk (codeRels c) w) =
      PresentedGroup.mk (amalgamRels c d edges) (relabel Sum.inl w) := by
  refine freeGroup_hom_eq_on_generators
    (f := (leftHom c d edges).comp (PresentedGroup.mk (codeRels c)))
    (g := (PresentedGroup.mk (amalgamRels c d edges)).comp
      (relabel Sum.inl)) ?_ w
  intro i
  change leftHom c d edges (PresentedGroup.of i) =
    PresentedGroup.of (Sum.inl i)
  exact PresentedGroup.toGroup.of _

theorem rightHom_mk (c d : PresentationCode) (edges : List (Raw × Raw))
    (w : FreeGroup (Fin (genCount d))) :
    rightHom c d edges (PresentedGroup.mk (codeRels d) w) =
      PresentedGroup.mk (amalgamRels c d edges) (relabel Sum.inr w) := by
  refine freeGroup_hom_eq_on_generators
    (f := (rightHom c d edges).comp (PresentedGroup.mk (codeRels d)))
    (g := (PresentedGroup.mk (amalgamRels c d edges)).comp
      (relabel Sum.inr)) ?_ w
  intro j
  change rightHom c d edges (PresentedGroup.of j) =
    PresentedGroup.of (Sum.inr j)
  exact PresentedGroup.toGroup.of _

theorem edgeHom_compatible (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    (leftHom c d edges).comp (leftEdgeHom c edges) =
      (rightHom c d edges).comp (rightEdgeHom d edges) := by
  ext p
  simp only [MonoidHom.comp_apply, leftEdgeHom, rightEdgeHom,
    FreeGroup.lift_apply_of, leftEdgeGenerator, rightEdgeGenerator]
  rw [leftHom_mk, rightHom_mk]
  apply mul_inv_eq_one.mp
  exact PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure
      (Or.inr ⟨p.1, p.2, rfl⟩))

def fromPush (c d : PresentationCode) (edges : List (Raw × Raw)) :
    Push c d edges →* PresentedGroup (amalgamRels c d edges) := by
  refine PushoutI.lift
    (fun b => match b with
      | false => leftHom c d edges
      | true => rightHom c d edges)
    ((leftHom c d edges).comp (leftEdgeHom c edges)) ?_
  intro b
  cases b with
  | false => rfl
  | true => exact (edgeHom_compatible c d edges).symm

@[simp] theorem toPush_of_inl (c d : PresentationCode)
    (edges : List (Raw × Raw)) (i : Fin (genCount c)) :
    toPush c d edges (PresentedGroup.of (Sum.inl i)) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        false (PresentedGroup.of i) :=
  PresentedGroup.toGroup.of _

@[simp] theorem toPush_of_inr (c d : PresentationCode)
    (edges : List (Raw × Raw)) (j : Fin (genCount d)) :
    toPush c d edges (PresentedGroup.of (Sum.inr j)) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        true (PresentedGroup.of j) :=
  PresentedGroup.toGroup.of _

@[simp] theorem fromPush_of_false (c d : PresentationCode)
    (edges : List (Raw × Raw)) (x : Carrier c) :
    fromPush c d edges
      (PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        false x) = leftHom c d edges x := by
  unfold fromPush
  rw [PushoutI.lift_of]
  rfl

@[simp] theorem fromPush_of_true (c d : PresentationCode)
    (edges : List (Raw × Raw)) (x : Carrier d) :
    fromPush c d edges
      (PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        true x) = rightHom c d edges x := by
  unfold fromPush
  rw [PushoutI.lift_of]
  rfl

theorem toPush_leftHom (c d : PresentationCode)
    (edges : List (Raw × Raw)) (x : Carrier c) :
    toPush c d edges (leftHom c d edges x) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        false x := by
  let f := (toPush c d edges).comp (leftHom c d edges)
  let g := PushoutI.of
    (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
    false
  have h : f = g := by
    refine MonoidHom.eq_of_eqOn_dense
      (PresentedGroup.closure_range_of (codeRels c)) ?_
    rintro _ ⟨i, rfl⟩
    change toPush c d edges
      (leftHom c d edges (PresentedGroup.of i)) = _
    rw [show leftHom c d edges (PresentedGroup.of i) =
        PresentedGroup.of (Sum.inl i) from PresentedGroup.toGroup.of _]
    exact toPush_of_inl c d edges i
  change f x = g x
  exact DFunLike.congr_fun h x

theorem toPush_rightHom (c d : PresentationCode)
    (edges : List (Raw × Raw)) (x : Carrier d) :
    toPush c d edges (rightHom c d edges x) =
      PushoutI.of
        (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
        true x := by
  let f := (toPush c d edges).comp (rightHom c d edges)
  let g := PushoutI.of
    (φ := Higman.Amalgam.famHom (leftEdgeHom c edges) (rightEdgeHom d edges))
    true
  have h : f = g := by
    refine MonoidHom.eq_of_eqOn_dense
      (PresentedGroup.closure_range_of (codeRels d)) ?_
    rintro _ ⟨j, rfl⟩
    change toPush c d edges
      (rightHom c d edges (PresentedGroup.of j)) = _
    rw [show rightHom c d edges (PresentedGroup.of j) =
        PresentedGroup.of (Sum.inr j) from PresentedGroup.toGroup.of _]
    exact toPush_of_inr c d edges j
  change f x = g x
  exact DFunLike.congr_fun h x

theorem toPush_fromPush (c d : PresentationCode)
    (edges : List (Raw × Raw)) (x : Push c d edges) :
    toPush c d edges (fromPush c d edges x) = x := by
  let f := (toPush c d edges).comp (fromPush c d edges)
  have h : f = MonoidHom.id (Push c d edges) := by
    refine PushoutI.hom_ext_nonempty ?_
    intro b
    cases b with
    | false =>
        refine MonoidHom.ext fun y => ?_
        exact toPush_leftHom c d edges y
    | true =>
        refine MonoidHom.ext fun y => ?_
        exact toPush_rightHom c d edges y
  change f x = x
  exact DFunLike.congr_fun h x

theorem fromPush_toPush (c d : PresentationCode)
    (edges : List (Raw × Raw))
    (x : PresentedGroup (amalgamRels c d edges)) :
    fromPush c d edges (toPush c d edges x) = x := by
  let f := (fromPush c d edges).comp (toPush c d edges)
  have h : f = MonoidHom.id (PresentedGroup (amalgamRels c d edges)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (PresentedGroup.closure_range_of (amalgamRels c d edges)) ?_
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
        change fromPush c d edges
          (toPush c d edges (PresentedGroup.of (Sum.inl i))) = _
        rw [toPush_of_inl, fromPush_of_false]
        exact PresentedGroup.toGroup.of _
    | inr j =>
        change fromPush c d edges
          (toPush c d edges (PresentedGroup.of (Sum.inr j))) = _
        rw [toPush_of_inr, fromPush_of_true]
        exact PresentedGroup.toGroup.of _
  change f x = x
  exact DFunLike.congr_fun h x

/-- The exact sum-alphabet quotient presentation is the two-factor pushout. -/
noncomputable def presentationEquivPush (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    PresentedGroup (amalgamRels c d edges) ≃* Push c d edges where
  toFun := toPush c d edges
  invFun := fromPush c d edges
  left_inv := fromPush_toPush c d edges
  right_inv := toPush_fromPush c d edges
  map_mul' := map_mul _

/-- The primitive-recursive amalgam code presents the pushout of the two coded
factors along the free group on the displayed edge-pair occurrences. -/
noncomputable def amalgamCodeEquivPush (c d : PresentationCode)
    (edges : List (Raw × Raw)) :
    Carrier (amalgamCode c d edges) ≃* Push c d edges :=
  (amalgamCodeEquivPresentation c d edges).trans
    (presentationEquivPush c d edges)

end AmalgamCodePushout
end GroupApproximation
