import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a closed dart walk at a repeated vertex

A pocket walk that is not simple visits some vertex twice.  Rotate the walk so that the vertex of
its first dart is visited again at position `k`.  Then the first `k` darts and the remaining darts
are two closed dart walks, the *lobes*, and the value read on the walk is the product of the values
read on the lobes.  So a walk that reads an element other than `1` has a lobe that reads an element
other than `1`.

* `IsClosedDartWalk`: a nonempty list of darts, each ending where the next begins, the last ending
  where the first begins.  `IsSimpleClosedWalk.isClosedDartWalk` drops the simplicity clauses.
* `IsClosedDartWalk.take` and `IsClosedDartWalk.drop`: the two lobes are closed dart walks.
* `listVal_dartWord_eq_mul_lobes` and `exists_lobe_listVal_ne_one`: the values.
* `pinchSplit`: everything at once.

Rotations are the consumer's step: `Embedded.listVal_dartWord_rotate` gives the conjugated value
of a rotated walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1): the pinched pocket walks of `OsinLemma94CaseOneSameCellStatement`.  It
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullSC

universe u w v

/-- **A closed dart walk.**  A nonempty list of darts in which each dart ends at the vertex where
the next one begins, and the last dart ends at the vertex where the first one begins.  Unlike
`IsSimpleClosedWalk`, vertices may repeat. -/
def IsClosedDartWalk (M : CombMap.{v}) (walk : List M.Dart) : Prop :=
  ∃ hne : walk ≠ [], walk.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
    M.vertexOf (M.alpha (walk.getLast hne)) = M.vertexOf (walk.head hne)

/-- A simple closed walk is a closed dart walk. -/
theorem IsSimpleClosedWalk.isClosedDartWalk {M : CombMap.{v}} {walk : List M.Dart}
    (hw : IsSimpleClosedWalk M walk) : IsClosedDartWalk M walk :=
  ⟨hw.ne_nil, hw.chain, hw.closes⟩

namespace IsClosedDartWalk

variable {M : CombMap.{v}} {walk : List M.Dart}

/-- **The first lobe.**  If a closed dart walk visits the vertex of its first dart again at
position `k`, with `0 < k`, its first `k` darts form a closed dart walk. -/
theorem take (hw : IsClosedDartWalk M walk) {k : ℕ} (hk0 : 0 < k) (hk : k < walk.length)
    (hpinch : M.vertexOf walk[0] = M.vertexOf walk[k]) :
    IsClosedDartWalk M (walk.take k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨_, hchain, _⟩ := hw
  have hchain' := List.isChain_iff_getElem.mp hchain
  have hlen : (walk.take (m + 1)).length = m + 1 := by
    rw [List.length_take]
    omega
  have hne : walk.take (m + 1) ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [hlen, List.length_nil] at h'
    omega
  refine ⟨hne, List.isChain_iff_getElem.mpr fun i hi => ?_, ?_⟩
  · have hi' : i + 1 < walk.length := by
      rw [hlen] at hi
      omega
    simpa only [List.getElem_take] using hchain' i hi'
  · have h := hchain' m (by omega)
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    simp only [List.getElem_take, hlen, Nat.add_sub_cancel]
    exact h.trans hpinch.symm

/-- **The second lobe.**  If a closed dart walk visits the vertex of its first dart again at
position `k`, its darts from position `k` on form a closed dart walk. -/
theorem drop (hw : IsClosedDartWalk M walk) {k : ℕ} (hk : k < walk.length)
    (hpinch : M.vertexOf walk[0] = M.vertexOf walk[k]) :
    IsClosedDartWalk M (walk.drop k) := by
  obtain ⟨hne0, hchain, hclose⟩ := hw
  have hchain' := List.isChain_iff_getElem.mp hchain
  have hlen : (walk.drop k).length = walk.length - k := List.length_drop
  have hne : walk.drop k ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [hlen, List.length_nil] at h'
    omega
  refine ⟨hne, List.isChain_iff_getElem.mpr fun i hi => ?_, ?_⟩
  · have hi' : k + i + 1 < walk.length := by
      rw [hlen] at hi
      omega
    simpa only [List.getElem_drop, Nat.add_assoc] using hchain' (k + i) hi'
  · rw [List.getLast_eq_getElem, List.head_eq_getElem] at hclose ⊢
    have hidx : k + (walk.length - k - 1) = walk.length - 1 := by omega
    simp only [List.getElem_drop, hlen, hidx, Nat.add_zero]
    exact hclose.trans hpinch

end IsClosedDartWalk

section Values

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- **The value of a walk is the product of the values of its two parts.** -/
theorem listVal_dartWord_eq_mul_lobes (Delta : DiscDiagram.{u, w, v} W)
    (walk : List Delta.toCombMap.Dart) (k : ℕ) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta walk) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take k)) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.drop k)) := by
  conv_lhs => rw [← List.take_append_drop k walk]
  rw [Embedded.dartWord_append, RelWord.listVal_append]

/-- **A walk reading an element other than `1` has a part reading an element other than `1`.** -/
theorem exists_lobe_listVal_ne_one (Delta : DiscDiagram.{u, w, v} W)
    {walk : List Delta.toCombMap.Dart}
    (hval : GGT.RelLetter.listVal (Embedded.dartWord Delta walk) ≠ 1) (k : ℕ) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take k)) ≠ 1 ∨
      GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.drop k)) ≠ 1 := by
  by_cases h1 : GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take k)) = 1
  · refine Or.inr fun h2 => hval ?_
    rw [listVal_dartWord_eq_mul_lobes Delta walk k, h1, h2, mul_one]
  · exact Or.inl h1

/-- **The pinch split.**  A closed dart walk that visits the vertex of its first dart again at
position `k`, with `0 < k`, is the concatenation of two nonempty closed dart walks.  If the walk
reads an element other than `1`, one of the two lobes does. -/
theorem pinchSplit (Delta : DiscDiagram.{u, w, v} W) {walk : List Delta.toCombMap.Dart}
    (hw : IsClosedDartWalk Delta.toCombMap walk) {k : ℕ} (hk0 : 0 < k) (hk : k < walk.length)
    (hpinch : Delta.toCombMap.vertexOf walk[0] = Delta.toCombMap.vertexOf walk[k])
    (hval : GGT.RelLetter.listVal (Embedded.dartWord Delta walk) ≠ 1) :
    ∃ lobe₁ lobe₂ : List Delta.toCombMap.Dart,
      walk = lobe₁ ++ lobe₂ ∧ lobe₁.length = k ∧ lobe₂.length = walk.length - k ∧
        IsClosedDartWalk Delta.toCombMap lobe₁ ∧ IsClosedDartWalk Delta.toCombMap lobe₂ ∧
        (GGT.RelLetter.listVal (Embedded.dartWord Delta lobe₁) ≠ 1 ∨
          GGT.RelLetter.listVal (Embedded.dartWord Delta lobe₂) ≠ 1) := by
  refine ⟨walk.take k, walk.drop k, (List.take_append_drop k walk).symm, ?_, List.length_drop,
    hw.take hk0 hk hpinch, hw.drop hk hpinch, exists_lobe_listVal_ne_one Delta hval k⟩
  rw [List.length_take]
  omega

/-- **Excising a front lobe that reads `1`.**  If the first `k` darts read `1`, the remaining darts
read the value of the walk.  Together with `IsClosedDartWalk.drop` this removes a lobe; to excise a
lobe elsewhere, rotate it to the front first (`ClosedWalkFaceColouring.closedChain_append_comm`,
through `isClosedDartWalk_iff_closedChain`). -/
theorem listVal_dartWord_drop_eq_of_take_eq_one (Delta : DiscDiagram.{u, w, v} W)
    (walk : List Delta.toCombMap.Dart) (k : ℕ)
    (htake : GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take k)) = 1) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.drop k)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta walk) := by
  rw [listVal_dartWord_eq_mul_lobes Delta walk k, htake, one_mul]

end Values

/-- **A closed dart walk is a nonempty closed chain.**  The chain-level split and rotation are on
main as `ClosedWalkFaceColouring.closedChain_split` and `closedChain_append_comm`, so the
combinatorial half of `IsClosedDartWalk.take` and `.drop` is subsumed there.  This module adds the
values. -/
theorem isClosedDartWalk_iff_closedChain {M : CombMap.{v}} {walk : List M.Dart} :
    IsClosedDartWalk M walk ↔
      walk ≠ [] ∧
        ClosedWalkFaceColouring.ClosedChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
          walk := by
  constructor
  · rintro ⟨hne, hc, hclose⟩
    exact ⟨hne, (ClosedWalkFaceColouring.closedChain_iff hne).mpr ⟨hc, hclose⟩⟩
  · rintro ⟨hne, h⟩
    obtain ⟨hc, hclose⟩ := (ClosedWalkFaceColouring.closedChain_iff hne).mp h
    exact ⟨hne, hc, hclose⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_drop_eq_of_take_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.isClosedDartWalk_iff_closedChain

#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.isClosedDartWalk
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.take
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.drop
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_mul_lobes
#audit_axioms GroupApproximation.GGT.VanKampen.exists_lobe_listVal_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.pinchSplit
