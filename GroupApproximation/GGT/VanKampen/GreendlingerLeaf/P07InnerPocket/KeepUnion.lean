import GroupApproximation.GGT.VanKampen.ClosedWalkFirstTurnEnclosure
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the map on the edges of three touching walks is connected

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b): the pocket between two regions `a`, `b` is read off the map on the edges of the
pocket walk `K` and of the two region cycles (lane gl-p07-01).

## The mathematical proof

Let `c₁, c₂, c₃` be dart walks, each chained at vertices (every dart ends where the next starts),
with `c₂` and `c₃` each starting a dart at a vertex where `c₁` starts a dart.  Let `N` be the map
on the union of their edges (`CombMap.PredicateRestriction.toCombMap`), with vertex rotation the
first return of the ambient rotation.

1. *Same ambient vertex ⇒ joined in `N`.*  The rotation of `N` is the first return of the ambient
   rotation, so its cycles are the ambient cycles meeting the kept set
   (`PermFirstReturn.sameCycle_iff`); rotation steps join one cycle
   (`NoncrossingClosedWalkSides.eqvGen_adjacent_of_sameCycle`).
2. *The edges of one walk are joined.*  By induction along the chain: from a walk dart `x` cross
   to `α x`, which starts at the vertex of the next walk dart, then use 1.  A dart whose reversal
   is a walk dart is one crossing from that walk dart.
3. *The union.*  Every kept dart is on an edge of some `c_k`; step 2 joins it to the touching dart
   of `c_k`, step 1 moves to the touching dart of `c₁`, and step 2 for `c₁` closes.

Neither planarity nor nonemptiness is used (the touching hypotheses supply the darts), so
`unionMap_connected` is stated without them; `keepUnion_connected` is the lane-shaped form.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Equiv SimpleClosedWalkSides

universe u

/-- The union of the edge sets of three walks is closed under edge reversal. -/
theorem keepUnion_alpha (M : CombMap.{u}) (c₁ c₂ c₃ : List M.Dart) (d : M.Dart) :
    (walkKeep M c₁ (M.alpha d) ∨ walkKeep M c₂ (M.alpha d) ∨ walkKeep M c₃ (M.alpha d)) ↔
      (walkKeep M c₁ d ∨ walkKeep M c₂ d ∨ walkKeep M c₃ d) := by
  simp only [walkKeep_alpha]

/-- The map on the edges of three walks. -/
noncomputable abbrev unionMap (M : CombMap.{u}) (c₁ c₂ c₃ : List M.Dart) : CombMap.{u} :=
  CombMap.PredicateRestriction.toCombMap M
    (fun d => walkKeep M c₁ d ∨ walkKeep M c₂ d ∨ walkKeep M c₃ d) (keepUnion_alpha M c₁ c₂ c₃)

section General

variable {M : CombMap.{u}} {keep : M.Dart → Prop} {hkeep : ∀ d, keep (M.alpha d) ↔ keep d}

/-- **Step 1.**  Kept darts at one ambient vertex are joined in the restricted map. -/
theorem eqvGen_adjacent_of_vertexOf_eq
    {x y : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (h : M.vertexOf x.1 = M.vertexOf y.1) :
    Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent x y :=
  NoncrossingClosedWalkSides.eqvGen_adjacent_of_sameCycle _
    ((PermFirstReturn.sameCycle_iff _ _ _
      (CombMap.PredicateRestriction.isRestriction M keep hkeep).sigma_firstReturn x y).mpr
      ((M.vertexOf_eq_iff _ _).mp h))

/-- **Step 2.**  In a restriction keeping the edges of a vertex-chained walk, any two darts on
edges of the walk are joined. -/
theorem eqvGen_adjacent_of_walk {c : List M.Dart} (hsub : ∀ x, walkKeep M c x → keep x)
    (hch : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    {x y : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart}
    (hx : walkKeep M c x.1) (hy : walkKeep M c y.1) :
    Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent x y := by
  have hne : c ≠ [] := by
    rcases hx with h | h
    · exact List.ne_nil_of_mem h
    · exact List.ne_nil_of_mem h
  have hmem : ∀ z ∈ c, ∀ hz : keep z,
      Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent
        ⟨c.head hne, hsub _ (Or.inl (List.head_mem hne))⟩ ⟨z, hz⟩ := by
    refine List.IsChain.induction (fun z => ∀ hz : keep z,
      Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent
        ⟨c.head hne, hsub _ (Or.inl (List.head_mem hne))⟩ ⟨z, hz⟩)
      c (List.IsChain.iff_mem.mp hch) ?_ ?_
    · rintro z w ⟨hzc, _, hzw⟩ hp hw
      have hαz : keep (M.alpha z) := hsub _ (Or.inr (by rw [M.alpha_involutive z]; exact hzc))
      refine Relation.EqvGen.trans _ _ _ (hp (hsub z (Or.inl hzc)))
        (Relation.EqvGen.trans _ ⟨M.alpha z, hαz⟩ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_)
      exact eqvGen_adjacent_of_vertexOf_eq (x := ⟨M.alpha z, hαz⟩) (y := ⟨w, hw⟩) hzw
    · intro lne hz
      exact Relation.EqvGen.refl _
  have hall : ∀ z : (CombMap.PredicateRestriction.toCombMap M keep hkeep).Dart,
      walkKeep M c z.1 →
      Relation.EqvGen (CombMap.PredicateRestriction.toCombMap M keep hkeep).Adjacent
        ⟨c.head hne, hsub _ (Or.inl (List.head_mem hne))⟩ z := by
    rintro ⟨z, hz⟩ hzk
    rcases hzk with h | h
    · exact hmem z h hz
    · exact Relation.EqvGen.trans _ _ _ (hmem (M.alpha z) h (hsub _ (Or.inl h)))
        (Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext (M.alpha_involutive z))))
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall x hx)) (hall y hy)

end General

/-- **The map on the edges of three touching walks is connected.**  Each walk is chained at
vertices, and the second and third walks each start a dart at a vertex where the first starts a
dart. -/
theorem unionMap_connected {M : CombMap.{u}} {c₁ c₂ c₃ : List M.Dart}
    (hch₁ : c₁.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hch₂ : c₂.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hch₃ : c₃.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (h₂ : ∃ d ∈ c₂, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e)
    (h₃ : ∃ d ∈ c₃, ∃ e ∈ c₁, M.vertexOf d = M.vertexOf e) :
    (unionMap M c₁ c₂ c₃).IsConnected := by
  obtain ⟨d₂, hd₂, e₂, he₂, hv₂⟩ := h₂
  obtain ⟨d₃, hd₃, e₃, he₃, hv₃⟩ := h₃
  have k₁ : ∀ x, walkKeep M c₁ x →
      (walkKeep M c₁ x ∨ walkKeep M c₂ x ∨ walkKeep M c₃ x) := fun _ h => Or.inl h
  have k₂ : ∀ x, walkKeep M c₂ x →
      (walkKeep M c₁ x ∨ walkKeep M c₂ x ∨ walkKeep M c₃ x) := fun _ h => Or.inr (Or.inl h)
  have k₃ : ∀ x, walkKeep M c₃ x →
      (walkKeep M c₁ x ∨ walkKeep M c₂ x ∨ walkKeep M c₃ x) := fun _ h => Or.inr (Or.inr h)
  have hall : ∀ x : (unionMap M c₁ c₂ c₃).Dart,
      Relation.EqvGen (unionMap M c₁ c₂ c₃).Adjacent ⟨e₂, k₁ _ (Or.inl he₂)⟩ x := by
    rintro ⟨x, hx⟩
    rcases hx with hx | hx | hx
    · exact eqvGen_adjacent_of_walk (hkeep := keepUnion_alpha M c₁ c₂ c₃) k₁ hch₁
        (x := ⟨e₂, k₁ _ (Or.inl he₂)⟩) (y := ⟨x, k₁ _ hx⟩) (Or.inl he₂) hx
    · exact Relation.EqvGen.trans _ ⟨d₂, k₂ _ (Or.inl hd₂)⟩ _
        (eqvGen_adjacent_of_vertexOf_eq (hkeep := keepUnion_alpha M c₁ c₂ c₃)
          (x := ⟨e₂, k₁ _ (Or.inl he₂)⟩) (y := ⟨d₂, k₂ _ (Or.inl hd₂)⟩) hv₂.symm)
        (eqvGen_adjacent_of_walk (hkeep := keepUnion_alpha M c₁ c₂ c₃) k₂ hch₂
          (x := ⟨d₂, k₂ _ (Or.inl hd₂)⟩) (y := ⟨x, k₂ _ hx⟩) (Or.inl hd₂) hx)
    · exact Relation.EqvGen.trans _ ⟨e₃, k₁ _ (Or.inl he₃)⟩ _
        (eqvGen_adjacent_of_walk (hkeep := keepUnion_alpha M c₁ c₂ c₃) k₁ hch₁
          (x := ⟨e₂, k₁ _ (Or.inl he₂)⟩) (y := ⟨e₃, k₁ _ (Or.inl he₃)⟩) (Or.inl he₂)
          (Or.inl he₃))
        (Relation.EqvGen.trans _ ⟨d₃, k₃ _ (Or.inl hd₃)⟩ _
          (eqvGen_adjacent_of_vertexOf_eq (hkeep := keepUnion_alpha M c₁ c₂ c₃)
            (x := ⟨e₃, k₁ _ (Or.inl he₃)⟩) (y := ⟨d₃, k₃ _ (Or.inl hd₃)⟩) hv₃.symm)
          (eqvGen_adjacent_of_walk (hkeep := keepUnion_alpha M c₁ c₂ c₃) k₃ hch₃
            (x := ⟨d₃, k₃ _ (Or.inl hd₃)⟩) (y := ⟨x, k₃ _ hx⟩) (Or.inl hd₃) hx))
  intro d e
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall d)) (hall e)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.keepUnion_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.eqvGen_adjacent_of_vertexOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.eqvGen_adjacent_of_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.unionMap_connected
