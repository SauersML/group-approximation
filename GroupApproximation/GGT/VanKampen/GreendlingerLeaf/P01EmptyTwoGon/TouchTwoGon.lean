import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.Proof
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BipartiteFaceDegree
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapSmallFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: a touch two-gon is a corner of a polygon

Notation: `M = S.diagram.toCombMap`, `φ = σ α` its face rotation, `N = contactMap P` (the
first-return restriction of `M.dual` to the retained darts `ContactKeep`), `f = φ_N`.  A dart of
`N` of colour `true` is a representative `rep k o h`, based at the polygon face `P.face k` with
reverse based at `objectFace S o`.  A dart of colour `false` is the reverse of one.  `f` flips the colour.

## The reduction (proved here)

Let `F` be a touch two-gon: a nondegenerate small face of `N` holding no object and held by no
selected region.  We derive `CornerExcluded P → False` (`false_of_touch_face`), so
`EmptyTouchTwoGonStatement` follows from `TouchCornerStatement` with `K = 0`
(`touchTwoGon_of_corner`).  Then `OsinLemma94ContactMapEmptyTwoGonInput` follows by
`proof_of_touch` (`proof_of_corner`).

1. *Degree four.*  Take `x₀` of colour `false` on `F` (`exists_colour_false`).  The degree of `F`
   is `< 6`, even (the colour alternates, `colour_facePerm_pow`) and `≥ 4`
   (`four_le_faceDegree_contactMap`), so it is `4` and `f⁴ x₀ = x₀` (`facePerm_four`).  Every dart
   of `F` is one of `x₀, f x₀, f² x₀, f³ x₀` (`eq_of_faceOf_eq_four`).
2. *The vertices.*  Put `d = α x₀` (a representative at polygon `k`, across object `o`).  Then
   `f x₀ = σ_N d` lies at the same vertex `k` and is a representative across an object `o₁`.
   `f² x₀` is based at `o₁` (a vertex of `N` is a face of `M`, `faceOf_facePerm_val`), and `f³ x₀`
   is a representative at a polygon `k′` across `o`, since `f⁴ x₀ = x₀`.
   * `o ≠ o₁`: otherwise `σ_N d` and `d` join the same two vertices, so they are equal
     (`contactMap_simple`), against `σ_N d ≠ d` (`contactMap_sigma_ne`); see `touch_object_ne`.
   * `k ≠ k′`: nondegeneracy applied to `f x₀`.
   * `k′` has a dart across `o` (`f³ x₀`) and a dart across `o₁` (`α (f² x₀)`); see
     `touch_witnesses`.
3. *The corner.*  `σ_N d = φ^m d` for the first return time `m` (`φ = σ_{M.dual}`).  For
   `0 < i < m` the dart `dᵢ = φ^i d` of the boundary of `k` is not retained, and it is in the class
   of `x₀`.  So `α dᵢ` is in the class of `x₀` (`restriction_facePerm_interior`), which gives:
   * the face across `dᵢ` lies in no selected region, otherwise `F` is region-held;
   * if the face across `dᵢ` is an object `p`, then `p ∈ {o, o₁}`.  Otherwise `F` holds `p`,
     since no dart of `F` is based at `objectFace p` (`object_of_not_holds`).
   With `φ^m d = (f x₀).1` across `o₁`, these are exactly the hypotheses of `CornerExcluded P` at
   `(k, k′, o, o₁, d, m)`.

## The residual (open): `TouchCornerStatement`

Under the binders of the target (no constant `K`), for a maximal `P`, no polygon `k` has a boundary
stretch `d, φ d, …, φ^m d` of this shape:
* it runs from a dart across `o` to a dart across `o′ ≠ o`;
* every interior dart faces no selected region, and faces no object other than `o` or `o′`;
* a second polygon `k′ ≠ k` also touches both `o` and `o′`.

Sketch (not formalized):
* Pick a switch between two distinct objects along the stretch with only non-object darts in
  between.  An interior dart with face `k` on both sides is a bridge of the planar map `M`.  The
  boundary walk of `k′` joins the `o`-boundary to the `o′`-boundary while avoiding those bridges,
  so the bridge path between the two contacts is closed off.  A closed bridge path has a leaf
  `φ c = α c`, which `S.DartMinimal` excludes (`not_leaf_of_dartMinimal` with
  `pendantPathRemovalInput`).  So the two contacts meet at one corner of `k`.
* Carve a triangle across `k` at that corner (`exists_split_corner_output`, transported by
  `insertionTransport`).  It is a singleton contiguity region along `o` and `o′`
  (`ContiguityGeometry.ofSingletonFace`), avoided by every selected region, which contradicts the
  weight maximality of `S` (`false_of_avoided_singleton`).
* Edge cases: label cancellation at the carved corner, and loop triangles (`CornerJoin`, the
  bubble lemmas).  A different polygon `k″` across an interior dart must be merged into `k` first.
  The two-sided bubble `false_of_twoCellSides` refutes the older "pocket model" in `Proof`.
* Neither `k′` nor the interior restrictions can be dropped: without them there are bridge
  corridors where the statement fails.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

/-- **The interior of a first-return face step**: the skipped darts are not retained and lie in the
face class of the starting dart. -/
theorem restriction_facePerm_interior (N : CombMap.{v}) (keep : N.Dart → Prop)
    (hkeep : ∀ d, keep (N.alpha d) ↔ keep d)
    (b : (CombMap.PredicateRestriction.toCombMap N keep hkeep).Dart) :
    ∃ m : ℕ, 0 < m ∧
      (N.sigma ^ m) (N.alpha b.1) =
        ((CombMap.PredicateRestriction.toCombMap N keep hkeep).facePerm b).1 ∧
      ∀ i : ℕ, 0 < i → i < m → ¬ keep ((N.sigma ^ i) (N.alpha b.1)) ∧
        Relation.EqvGen (CombMap.FaceClassStep N keep) b.1 ((N.sigma ^ i) (N.alpha b.1)) := by
  obtain ⟨m, hm, heq, hskip⟩ := CombMap.PredicateRestriction.sigma_firstReturn N keep
    (CombMap.PredicateRestriction.alpha N keep hkeep b)
  have hnot : ∀ i, 0 < i → i < m → ¬ keep ((N.sigma ^ i) (N.alpha b.1)) := fun i hi him hk' =>
    hskip i hi him ⟨⟨_, hk'⟩, rfl⟩
  have key : ∀ k, 0 < k → k ≤ m →
      Relation.EqvGen (CombMap.FaceClassStep N keep) b.1 ((N.sigma ^ k) (N.alpha b.1)) := by
    intro k hk hkm
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [zero_add, pow_one]
        exact Relation.EqvGen.rel _ _ (Or.inl rfl)
      · have hy : ¬ keep ((N.sigma ^ k) (N.alpha b.1)) := hnot k hkpos (by omega)
        have h1 : Relation.EqvGen (CombMap.FaceClassStep N keep) ((N.sigma ^ k) (N.alpha b.1))
            (N.sigma ((N.sigma ^ k) (N.alpha b.1))) :=
          Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨hy, rfl⟩))
            (Relation.EqvGen.rel _ _ (Or.inl (facePerm_alpha_eq_sigma N _).symm))
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (ih hkpos (by omega)) h1
  have h4 : (N.sigma ^ m) (N.alpha b.1) =
      ((CombMap.PredicateRestriction.toCombMap N keep hkeep).facePerm b).1 := heq
  exact ⟨m, hm, h4, fun i hi him => ⟨hnot i hi him, key i hi him.le⟩⟩

section TouchTwoGon

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- A face step of the contact map lands at the vertex across the edge. -/
theorem faceOf_facePerm_val (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart) :
    S.diagram.toCombMap.faceOf (P.contactMap.facePerm x).1 =
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x.1) :=
  P.faceOf_eq_of_vertexOf_eq (P.contactMap.vertexOf_sigma (P.contactMap.alpha x))

/-- A face step of the contact map flips the colour. -/
theorem colour_facePerm (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart) :
    P.contactColour (P.contactMap.facePerm x) = !P.contactColour x := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, P.contactColour_sigma, P.contactColour_alpha]

/-- A dart of colour `true` is based at a polygon and faces an object. -/
theorem faces_of_colour_true (P : OsinLemma94RealizedPolygons S) {y : P.contactMap.Dart}
    (hy : P.contactColour y = true) :
    ∃ k : Fin P.count, ∃ o : Option (Fin S.diagram.rCellCount),
      S.diagram.toCombMap.faceOf y.1 = P.face k ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y.1) =
        OsinLemma94RealizedPolygons.objectFace S o := by
  obtain ⟨k, o, h, -, hk⟩ := (P.contactColour_eq_true_iff y).mp hy
  exact ⟨k, o, by rw [hk, P.faceOf_rep], by rw [hk, P.faceOf_alpha_rep]⟩

/-- **Step 1: a small face of the contact map has degree four.** -/
theorem facePerm_four (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart)
    (hdeg : P.contactMap.faceDegree (P.contactMap.faceOf x) < 6) :
    P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm
      (P.contactMap.facePerm x))) = x := by
  classical
  obtain ⟨l, hl, hhead⟩ := P.contactMap.exists_isFaceCycle_head x
  have hlen : l.length = P.contactMap.faceDegree (P.contactMap.faceOf x) := by
    rw [hl.length_eq, hhead]
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hl.ne_nil
  have hper : (P.contactMap.facePerm ^ l.length) x = x := by
    have h := OsinUnboundSameCellCycle.pow_length hl.toFaceBoundary (k := 0) hpos
    have h0 : hl.toFaceBoundary.darts[0]'hpos = x := by
      show l[0]'hpos = x
      rw [List.getElem_zero]
      exact hhead
    rw [h0] at h
    exact h
  have hodd : ¬ l.length % 2 = 1 := by
    intro hodd
    obtain ⟨t, ht⟩ : ∃ t, l.length = 2 * t + 1 := ⟨l.length / 2, by omega⟩
    have h := (CombMap.colour_facePerm_pow P.contactColour P.contactColour_alpha
      P.contactColour_sigma x t).2
    rw [← ht, hper] at h
    cases hcx : P.contactColour x <;> simp [hcx] at h
  have h4 := P.four_le_faceDegree_contactMap (P.contactMap.faceOf x)
  have hl4 : l.length = 4 := by omega
  rw [hl4, pow_succ', pow_succ', pow_succ', pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply] at hper
  exact hper

/-- The darts of a face of degree four. -/
theorem eq_of_faceOf_eq_four (P : OsinLemma94RealizedPolygons S) {x₀ z : P.contactMap.Dart}
    (hper : P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm
      (P.contactMap.facePerm x₀))) = x₀)
    (hz : P.contactMap.faceOf z = P.contactMap.faceOf x₀) :
    z = x₀ ∨ z = P.contactMap.facePerm x₀ ∨ z = P.contactMap.facePerm (P.contactMap.facePerm x₀) ∨
      z = P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀)) := by
  have key : ∀ j : ℕ, (P.contactMap.facePerm ^ j) x₀ = x₀ ∨
      (P.contactMap.facePerm ^ j) x₀ = P.contactMap.facePerm x₀ ∨
      (P.contactMap.facePerm ^ j) x₀ = P.contactMap.facePerm (P.contactMap.facePerm x₀) ∨
      (P.contactMap.facePerm ^ j) x₀ =
        P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀)) := by
    intro j
    induction j with
    | zero =>
      refine Or.inl ?_
      rw [pow_zero, Equiv.Perm.one_apply]
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h | h | h <;> rw [h]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl hper
  obtain ⟨j, hj⟩ := ((P.contactMap.faceOf_eq_iff x₀ z).mp hz.symm).exists_nat_pow_eq
  rw [← hj]
  exact key j

/-- **Step 3b: an object across the class of a touch two-gon is one of its two vertices.** -/
theorem object_of_not_holds (P : OsinLemma94RealizedPolygons S) {F : P.contactMap.Face}
    (hnh : ¬ P.HoldsObject F) {x₀ : P.contactMap.Dart} (hF0 : P.contactMap.faceOf x₀ = F)
    (hper : P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm
      (P.contactMap.facePerm x₀))) = x₀)
    {o o₁ p : Option (Fin S.diagram.rCellCount)} {k k' : Fin P.count}
    (h0 : S.diagram.toCombMap.faceOf x₀.1 = OsinLemma94RealizedPolygons.objectFace S o)
    (h1 : S.diagram.toCombMap.faceOf (P.contactMap.facePerm x₀).1 = P.face k)
    (h2 : S.diagram.toCombMap.faceOf (P.contactMap.facePerm (P.contactMap.facePerm x₀)).1 =
      OsinLemma94RealizedPolygons.objectFace S o₁)
    (h3 : S.diagram.toCombMap.faceOf
      (P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀))).1 = P.face k')
    {y : S.diagram.toCombMap.Dart} (hcls : ContactClass P x₀.1 y)
    (hp : S.diagram.toCombMap.faceOf y = OsinLemma94RealizedPolygons.objectFace S p) :
    p = o ∨ p = o₁ := by
  by_contra hne
  have hpo : p ≠ o := fun h => hne (Or.inl h)
  have hpo₁ : p ≠ o₁ := fun h => hne (Or.inr h)
  apply hnh
  unfold OsinLemma94RealizedPolygons.HoldsObject
  refine ⟨x₀, hF0, y, hcls, p, hp, fun z hz hzp => ?_⟩
  have hz' : P.contactMap.faceOf z = P.contactMap.faceOf x₀ := hz.trans hF0.symm
  rcases eq_of_faceOf_eq_four P hper hz' with e | e | e | e <;> rw [e] at hzp
  · exact hpo (OsinLemma94RealizedPolygons.objectFace_injective S (hzp.symm.trans h0))
  · exact OsinLemma94RealizedPolygons.objectFace_ne_face P k p (hzp.symm.trans h1)
  · exact hpo₁ (OsinLemma94RealizedPolygons.objectFace_injective S (hzp.symm.trans h2))
  · exact OsinLemma94RealizedPolygons.objectFace_ne_face P k' p (hzp.symm.trans h3)

/-- **Step 2a: the two objects of a small face are distinct.** -/
theorem touch_object_ne (P : OsinLemma94RealizedPolygons S) {x₀ : P.contactMap.Dart}
    (hx₀c : P.contactColour x₀ = false) {o o₁ : Option (Fin S.diagram.rCellCount)}
    (hx₀o : S.diagram.toCombMap.faceOf x₀.1 = OsinLemma94RealizedPolygons.objectFace S o)
    (hy₁o : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (P.contactMap.facePerm x₀).1) =
      OsinLemma94RealizedPolygons.objectFace S o₁) :
    o ≠ o₁ := by
  intro hoo
  have hac : P.contactColour (P.contactMap.alpha x₀) = true := by
    rw [P.contactColour_alpha, hx₀c, Bool.not_false]
  refine P.contactMap_sigma_ne (P.contactMap.alpha x₀) hac ?_
  refine P.contactMap_simple _ _ (P.contactMap.vertexOf_sigma _) ?_
  refine P.vertexOf_eq_of_faceOf_eq ?_
  show S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (P.contactMap.facePerm x₀).1) =
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x₀.1))
  rw [hy₁o, S.diagram.toCombMap.alpha_involutive, hx₀o, hoo]

/-- **Step 2c: the second polygon of a small face touches both objects.** -/
theorem touch_witnesses (P : OsinLemma94RealizedPolygons S) {x₀ : P.contactMap.Dart}
    (hper : P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm
      (P.contactMap.facePerm x₀))) = x₀)
    {k' : Fin P.count} {o o₁ : Option (Fin S.diagram.rCellCount)}
    (hx₀o : S.diagram.toCombMap.faceOf x₀.1 = OsinLemma94RealizedPolygons.objectFace S o)
    (hy₂o : S.diagram.toCombMap.faceOf (P.contactMap.facePerm (P.contactMap.facePerm x₀)).1 =
      OsinLemma94RealizedPolygons.objectFace S o₁)
    (hy₃k : S.diagram.toCombMap.faceOf
      (P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀))).1 = P.face k') :
    (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o) ∧
    (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o₁) := by
  have e1 := faceOf_facePerm_val P
    (P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀)))
  rw [hper] at e1
  refine ⟨⟨(P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀))).1, hy₃k,
    e1.symm.trans hx₀o⟩, ⟨S.diagram.toCombMap.alpha
      (P.contactMap.facePerm (P.contactMap.facePerm x₀)).1,
    (faceOf_facePerm_val P (P.contactMap.facePerm (P.contactMap.facePerm x₀))).symm.trans hy₃k,
    ?_⟩⟩
  rw [S.diagram.toCombMap.alpha_involutive]
  exact hy₂o

/-- **The corner configuration**: a polygon `k` whose boundary runs from a dart across `o` to a
dart across `o′ ≠ o`, through darts facing no selected region and no object but `o` and `o′`, while
a second polygon `k′` touches both `o` and `o′`. -/
def CornerExcluded (P : OsinLemma94RealizedPolygons S) : Prop :=
  ∀ k k' : Fin P.count, k ≠ k' →
    ∀ o o' : Option (Fin S.diagram.rCellCount), o ≠ o' →
      ∀ (d : S.diagram.toCombMap.Dart) (m : ℕ), 0 < m →
        S.diagram.toCombMap.faceOf d = P.face k →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
          OsinLemma94RealizedPolygons.objectFace S o →
        S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ m) d)) =
          OsinLemma94RealizedPolygons.objectFace S o' →
        (∀ i : ℕ, 0 < i → i < m →
          (∀ a ∈ S.family, S.diagram.toCombMap.faceOf
            (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) ∉ a.1) ∧
          ∀ p : Option (Fin S.diagram.rCellCount), S.diagram.toCombMap.faceOf
            (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ i) d)) =
              OsinLemma94RealizedPolygons.objectFace S p → p = o ∨ p = o') →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o) →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o') →
        False

/-- The vertex data of a small face, from a dart of colour `false`. -/
theorem touch_vertices (P : OsinLemma94RealizedPolygons S) {x₀ : P.contactMap.Dart}
    (hx₀c : P.contactColour x₀ = false) :
    ∃ (k k' : Fin P.count) (o o₁ : Option (Fin S.diagram.rCellCount)),
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x₀.1) = P.face k ∧
      S.diagram.toCombMap.faceOf x₀.1 = OsinLemma94RealizedPolygons.objectFace S o ∧
      S.diagram.toCombMap.faceOf (P.contactMap.facePerm x₀).1 = P.face k ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (P.contactMap.facePerm x₀).1) =
        OsinLemma94RealizedPolygons.objectFace S o₁ ∧
      S.diagram.toCombMap.faceOf (P.contactMap.facePerm (P.contactMap.facePerm x₀)).1 =
        OsinLemma94RealizedPolygons.objectFace S o₁ ∧
      S.diagram.toCombMap.faceOf
        (P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀))).1 =
          P.face k' := by
  have hac : P.contactColour (P.contactMap.alpha x₀) = true := by
    rw [P.contactColour_alpha, hx₀c, Bool.not_false]
  have hy₁c : P.contactColour (P.contactMap.facePerm x₀) = true := by
    rw [colour_facePerm P, hx₀c, Bool.not_false]
  have hy₃c : P.contactColour
      (P.contactMap.facePerm (P.contactMap.facePerm (P.contactMap.facePerm x₀))) = true := by
    rw [colour_facePerm P, colour_facePerm P, colour_facePerm P, hx₀c, Bool.not_false,
      Bool.not_true, Bool.not_false]
  obtain ⟨k, o, hdk, hdo⟩ := faces_of_colour_true P hac
  obtain ⟨_, o₁, _, hy₁o⟩ := faces_of_colour_true P hy₁c
  obtain ⟨k', _, hy₃k, _⟩ := faces_of_colour_true P hy₃c
  have hx₀o : S.diagram.toCombMap.faceOf x₀.1 = OsinLemma94RealizedPolygons.objectFace S o := by
    rw [P.contactMap_alpha_val, S.diagram.toCombMap.alpha_involutive] at hdo
    exact hdo
  exact ⟨k, k', o, o₁, hdk, hx₀o, (faceOf_facePerm_val P x₀).trans hdk, hy₁o,
    (faceOf_facePerm_val P (P.contactMap.facePerm x₀)).trans hy₁o, hy₃k⟩

/-- **The reduction: a touch two-gon gives a corner configuration.** -/
theorem false_of_touch_face (P : OsinLemma94RealizedPolygons S) {F : P.contactMap.Face}
    (hnd : P.NondegenerateSmallFace F) (hnh : ¬ P.HoldsObject F)
    (hnr : ¬ ∃ a ∈ S.family, RegionHeld P F a) (hcorner : CornerExcluded P) : False := by
  obtain ⟨hdeg, hnd2⟩ := hnd
  obtain ⟨x, hx⟩ := Quotient.exists_rep F
  have hxF : P.contactMap.faceOf x = F := hx
  obtain ⟨x₀, hx₀F, hx₀c, -⟩ := exists_colour_false P x
  have hF0 : P.contactMap.faceOf x₀ = F := hx₀F.trans hxF
  have hper := facePerm_four P x₀ (by rw [hF0]; exact hdeg)
  obtain ⟨k, k', o, o₁, hdk, hx₀o, hy₁k, hy₁o, hy₂o, hy₃k⟩ := touch_vertices P hx₀c
  have hkk : k ≠ k' := by
    intro hkk
    refine hnd2 (P.contactMap.facePerm x₀) (by rw [P.contactMap.faceOf_facePerm, hF0]) ?_ ?_
    · rw [colour_facePerm P, hx₀c, Bool.not_false]
    · exact P.vertexOf_eq_of_faceOf_eq (by rw [hy₁k, hy₃k, hkk])
  obtain ⟨hw₀, hw₁⟩ := touch_witnesses P hper hx₀o hy₂o hy₃k
  obtain ⟨m, hm, hend, hint⟩ := restriction_facePerm_interior S.diagram.toCombMap.dual
    P.ContactKeep P.contactKeep_alpha x₀
  have hend' : (S.diagram.toCombMap.facePerm ^ m) (S.diagram.toCombMap.alpha x₀.1) =
      (P.contactMap.facePerm x₀).1 := hend
  refine hcorner k k' hkk o o₁ (touch_object_ne P hx₀c hx₀o hy₁o)
    (S.diagram.toCombMap.alpha x₀.1) m hm hdk (by rw [S.diagram.toCombMap.alpha_involutive]; exact hx₀o)
    ?_ ?_ hw₀ hw₁
  · rw [hend']
    exact hy₁o
  · intro i hi him
    have hcls : ContactClass P x₀.1 (S.diagram.toCombMap.alpha
        ((S.diagram.toCombMap.facePerm ^ i) (S.diagram.toCombMap.alpha x₀.1))) :=
      Relation.EqvGen.trans _ _ _ (hint i hi him).2
        (Relation.EqvGen.rel _ _ (Or.inr ⟨(hint i hi him).1, rfl⟩))
    refine ⟨fun a ha hmem => hnr ⟨a, ha, ?_⟩,
      fun p hp => object_of_not_holds P hnh hF0 hper hx₀o hy₁k hy₂o hy₃k hcls hp⟩
    unfold RegionHeld
    exact ⟨x₀, hF0, _, hcls, hmem⟩

end TouchTwoGon

/-- **The corner exclusion** (open residual): under the binders of
`OsinLemma94ContactMapEmptyTwoGonInput`, a maximal realized polygon family has no corner
configuration `CornerExcluded`. -/
def TouchCornerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal → CornerExcluded P

/-- **The touch two-gons from the corner exclusion**, with constant `0`: there are none. -/
theorem touchTwoGon_of_corner (hcorner : TouchCornerStatement.{u, w, v}) :
    EmptyTouchTwoGonStatement.{u, w, v} := by
  intro _ _ _ D hhyper lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e0, he0⟩ := hcorner D hhyper lambda c mu h1 h2 h3 h4 h5
  refine ⟨e0, fun eps heps => ?_⟩
  obtain ⟨r0, hr0, hK⟩ := he0 eps heps
  refine ⟨0, r0, hr0,
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax => ?_⟩
  have hexcl := hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax
  have hempty : ∀ F ∈ (Finset.univ.filter fun F : P.contactMap.Face =>
      P.NondegenerateSmallFace F ∧ ¬ P.HoldsObject F ∧ ¬ ∃ a ∈ S.family, RegionHeld P F a),
      False := by
    intro F hF
    obtain ⟨hnd, hnh, hnr⟩ := (Finset.mem_filter.mp hF).2
    exact false_of_touch_face P hnd hnh hnr hexcl
  exact (Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hempty)).le.trans
    (Nat.zero_le _)

/-- **The empty two-gon count from the corner exclusion** (reduction; the residual is open). -/
theorem proof_of_corner (hcorner : TouchCornerStatement.{u, w, v}) :
    OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v} :=
  proof_of_touch (touchTwoGon_of_corner hcorner)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.false_of_touch_face
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.touchTwoGon_of_corner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.proof_of_corner
