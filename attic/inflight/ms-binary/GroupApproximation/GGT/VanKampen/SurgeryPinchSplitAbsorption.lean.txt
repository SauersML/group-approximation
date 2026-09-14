import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitExtremal
import GroupApproximation.GGT.VanKampen.Estimating.SingletonFaceRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Absorbing a pinched bubble across a vertex splitting

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4.  A bubble between relator cells, or a lobe of
a relator cell around a `G`-face, can be pinched at a vertex.  Then it is not a contiguity
subdiagram, and no hypothesis of the counts bounds it.  Splitting the pinch vertex
(`PinchSplit.Input.diagram`, the vertex explosion) merges the two faces at the pinch into one
`G`-face of an O-equivalent diagram.  Every dart, label and relator cell is kept, and so is every
selected region that avoids both faces (`PinchSplit.transportSection`).  When the merged face reads
as an `ε`-contiguity region, adjoining it to the transported family gives a heavier legal family,
against `weight_maximal`.

On a lobe `h h' (hh')⁻¹` of a cell `Π` at a vertex `v`, enclosing a `G`-triangle `g`, the corners
at `v` read `Π`, `g`, `Π`, and the outer face `f` between the two visits.  Splitting `v` between
the corners of `g` and `f` splices the walk of `g` into the walk of `f`.  Where `f` read
`α e_out, α e_in`, it now reads `α e_out, α (hh')⁻¹, α h', α h, α e_in`, the reversed arc of `Π`
through the lobe.  So when `f` is unselected and reads an arc of `Π`, a short side, a target arc
and a short side, the merged face is a region whose source arc absorbs the lobe, and the family
weighs more.

* `GloballyDistinguishedSectionFamily.false_of_avoided_singleton`: a legal realized family at
  least as heavy as a distinguished family contradicts maximality, once it carries a singleton
  region at a face it avoids, with nonempty arcs and respecting the sections.
* `PinchSplit.Input.merged_noInternalFaceDart`: the merged face has no internal dart when no dart
  of the two pinch faces has its reverse on them, as `ContiguityGeometry.ofSingletonFace` asks.
* `PinchSplit.false_of_mergedRegion`, `PinchSplit.PinchSplitAbsorptionStatement`,
  `PinchSplit.pinchSplitAbsorption`: the absorption.

Not covered here.  A pinch face inside a selected region fails `Input.Avoids`, and absorbing it
needs a transport of that region through the merge.  A merged face that is not a contiguity region
is only merged, with the same weight (`PinchSplit.transportDistinguished`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **An avoided singleton region contradicts maximality.**  Let `T` be a legal realized section
family at least as heavy as the distinguished family `S`.  A singleton region at a face that no
region of `T` contains, with nonempty arcs and respecting the sections, adjoined to `T`, gives a
legal family heavier than `S`. -/
theorem false_of_avoided_singleton
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (T : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : T.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hweight : S.toRealizedSectionFamily.weight ≤ T.weight)
    {f : T.diagram.toCombMap.Face}
    (H : ContiguityGeometry D eps T.diagram ({f} : Finset T.diagram.toCombMap.Face))
    (havoid : ∀ a ∈ T.family, f ∉ a.1)
    (hrespects : RegionCandidate.RespectsSections cuts
      (⟨{f}, H⟩ : RegionCandidate D eps T.diagram))
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length) : False := by
  have hrespects2 : ∀ a ∈ Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps T.diagram) T.family
      (RegionCandidate.singleton_not_mem_of_avoid H havoid),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · exact hrespects
    · exact T.respects a ha2
  have hnondegenerate2 : ∀ a ∈ Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps T.diagram) T.family
      (RegionCandidate.singleton_not_mem_of_avoid H havoid),
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · exact ⟨hsource, htarget⟩
    · exact T.nondegenerate a ha2
  have hlt := RegionCandidate.familyWeight_lt_cons_singleton H havoid hsource
  have hle : EstimatingSelection.familyWeight RegionCandidate.weight
      (Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps T.diagram) T.family
        (RegionCandidate.singleton_not_mem_of_avoid H havoid)) ≤
      S.toRealizedSectionFamily.weight :=
    S.weight_maximal
      { diagram := T.diagram
        equiv := T.equiv
        reduced := T.reduced
        family := Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps T.diagram) T.family
          (RegionCandidate.singleton_not_mem_of_avoid H havoid)
        pairwise := RegionCandidate.cons_singleton_pairwise H havoid T.pairwise
        respects := hrespects2
        nondegenerate := hnondegenerate2 }
      (fun d => hlegal d)
  have hT : T.weight = EstimatingSelection.familyWeight RegionCandidate.weight T.family := rfl
  exact lt_irrefl _ (lt_of_lt_of_le hlt (hle.trans (hweight.trans_eq hT)))

end GloballyDistinguishedSectionFamily

namespace PinchSplit

namespace Input

variable {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)

/-- **The merged face has no internal dart** when no dart of the two pinch faces has its reverse
on one of them.  The split keeps every dart and the edge reversal, and sends the two pinch faces,
and only them, to the merged face. -/
theorem merged_noInternalFaceDart
    (hno : ∀ d : Delta.toCombMap.Dart,
      (Delta.toCombMap.faceOf d = I.leftFace ∨ Delta.toCombMap.faceOf d = I.rightFace) →
        ¬ (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = I.leftFace ∨
          Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = I.rightFace)) :
    Surgery.MapCollapse.NoInternalFaceDart I.diagram.toCombMap I.merged := by
  intro d hd hal
  have hd' : I.kept (Delta.toCombMap.faceOf d) = I.merged := hd
  have hal' : I.kept (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d)) = I.merged := hal
  exact hno d ((I.kept_eq_merged_iff _).mp hd') ((I.kept_eq_merged_iff _).mp hal')

end Input

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pinched bubble is absorbed.**  Split the diagram of a distinguished family at a pinch
whose two faces no selected region contains.  If the merged face reads as a contiguity region with
nonempty arcs respecting the sections, adjoining it to the transported family contradicts
maximality. -/
theorem false_of_mergedRegion
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1)
    (H : ContiguityGeometry D eps I.diagram ({I.merged} : Finset I.diagram.toCombMap.Face))
    (hrespects : RegionCandidate.RespectsSections cuts
      (⟨{I.merged}, H⟩ : RegionCandidate D eps I.diagram))
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length) : False :=
  S.false_of_avoided_singleton (transportSection S.toRealizedSectionFamily I havoid)
    (transportSection_labelLegal S.toRealizedSectionFamily I havoid _ S.label_admissible)
    (le_of_eq (transportSection_weight S.toRealizedSectionFamily I havoid).symm)
    (f := I.merged) H (I.regionFamily_avoid_merged S.family havoid) hrespects hsource htarget

/-- **The bubble un-pinch absorption.**  No distinguished section family has a pinch between two
`G`-faces that no selected region contains, whose merged face after the split is an `ε`-contiguity
region with nonempty arcs respecting the sections. -/
def PinchSplitAbsorptionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram),
    (∀ b ∈ S.family, I.Avoids b.1) →
      ∀ H : ContiguityGeometry D eps I.diagram ({I.merged} : Finset I.diagram.toCombMap.Face),
        RegionCandidate.RespectsSections cuts
            (⟨{I.merged}, H⟩ : RegionCandidate D eps I.diagram) →
          0 < H.sourceArc.length → 0 < H.targetArc.length → False

theorem pinchSplitAbsorption : PinchSplitAbsorptionStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S _ I havoid H hrespects hsource htarget
  exact false_of_mergedRegion S I havoid H hrespects hsource htarget

end PinchSplit

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.PinchSplit.pinchSplitAbsorption
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_avoided_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.merged_noInternalFaceDart
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.false_of_mergedRegion
