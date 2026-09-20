import GroupApproximation.GGT.VanKampen.CombMapRestrictionComponentFaceClasses
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: face-class basics

Target: `OsinLemma94ContactMapEmptyTwoGonInput` (`Estimating/OsinLemma94ContactMapHolds`).  Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.4: under the binders of `OsinLemma94LongTransitionInput`,
the nondegenerate faces of degree less than six of `contactMap P` holding no object number at most
`K n`, with `n = Delta.rCellCount`.

## Notation

`M = S.diagram.toCombMap` is the optimal diagram, `M*` its dual (same darts, `α* = α`, `σ* = φ`,
so `φ* = σ`).  `keep = P.ContactKeep` retains the representatives of rich polygons and their
reverses, and `N = contactMap P` is the first-return restriction of `M*` to `keep`.  The class
relation `x ∼ y` is `EqvGen (FaceClassStep M* keep)`: one step is `x ↦ σ x` (always), or
`x ↦ α x` when `x` is not retained.  So a non-retained `x` also steps to `φ x = σ (α x)`.

## The proof, case by case

**Step 1 (face steps of `N` are class paths).**  For a dart `b` of `N`, `φ_N b = σ*^m (α b)` with
`σ*^k (α b)` not retained for `0 < k < m` (first return).  Each `σ* = φ` step on a non-retained dart
is `α` then `σ`, so `b ∼ φ_N b` (`faceClass_restriction_facePerm`).  Hence every face of `N` has a
dart of colour `false` in the class of any of its darts (`exists_colour_false`): if `x` has colour
`true`, `φ_N x` has colour `false`.

**Step 2 (a face holding no object is determined by its class).**  Let `F` hold no object,
`x₁ ∈ F` and `x₁ ∼ x₂` (`faceOf_eq_of_not_holdsObject`).  Take `z ∼ x₂` with `z` in the face of `x₂`
and colour `false`; `z` is based at an object face `objectFace S o`.  Since `F` holds no object,
some `z′ ∈ F` is based at `objectFace S o`.  Then `x₁, z′` share a face of `N`, and `z′, z` are
based at one face of `M` hence at one vertex of `N`; so `x₁` and `z` lie in one component of `N`.
The separation theorem `faceOf_eq_of_faceClass_of_componentOf` (planarity of `M*`) gives
`N.faceOf x₁ = N.faceOf z = N.faceOf x₂`.

**Step 3 (a selected region lies in one class).**  Let `a ∈ S.family` and `d` a dart with
`faceOf d ∈ a.1`.
* `d` is not retained (`not_contactKeep_of_mem`): a representative is based at a polygon face, and
  polygon faces are unselected; the reverse of a representative is based at an object face, and
  the faces of a region are `G`-cells distinct from the exterior, while a relator cell of a
  least-area diagram has a nontrivial word.
* Consecutive boundary darts of `a` are joined by class paths: `φ` on a non-retained dart, then
  internal moves `φ ∘ α = σ`.  So all boundary darts are in the class of the base dart `c₀`
  (`contactClass_head_cycle`).
* Let `B x` be "`faceOf x ∈ a.1` and `x ≁ c₀`".  `B` is closed under `α` and `σ` in both directions:
  if `faceOf (α x) ∉ a.1` then `x` is a boundary dart, so `x ∼ c₀`; `σ x = φ (α x)` lies in the face
  of `α x`; and the non-retained darts `x, α x` step to `α x, σ x`.  Since `M` is connected, `B`
  would hold at a dart of the exterior, which is not in `a.1`.  So `faceOf d ∈ a.1 → c₀ ∼ d`
  (`contactClass_head_of_mem`).

**Step 4 (the region charge).**  Say `F` is region-held by `a` if some dart of `F` is in the class
of a dart based in `a.1`.  By Steps 2 and 3, a region holds at most one face holding no object
(`regionHeld_unique`), so these faces number at most `|S.family| ≤ 3 (n + r − 1) ≤ 12 n`
(`card_regionHeld_le`, `SectionCuts.count_le`, `0 < n`).

**Step 5 (the touch case, open).**  The remaining faces `F`: nondegenerate, degree `< 6`, holding
no object, region-held by no region.  `F` is a two-gon `(f, a, f′, b)` or a four-gon of the
bipartite contact map.  Its class meets only corners of the boundary objects and polygons of `F` and
darts of unselected `G`-faces, and every such unselected `G`-face is a polygon (`face_complete`).
The polygons inside are not rich along the boundary objects.  Charging these faces linearly in `n`
needs a bound on the multi-contacts of one pair of rich polygons through one pair of objects (the
touch components of `a` and `b` between `f` and `f′`), or an exclusion of the lens by maximality of
`P`.  Neither is in the corpus.
* Euler's formula on `N` gives `2E + 6 ≤ 3V + t` with `t` the number of small faces: it bounds
  `E` by `t`, not conversely, so it cannot bound `t`.
* `OsinLemma94ObjectTouchComponentsInput` and `OsinLemma94TwoGonHoldsInput` are open on main, and
  `ContactBubble` covers only polygons of side count two.
This residual is `EmptyTouchTwoGonStatement` (module `Proof`); `proof_of_touch` reduces the target
to it with constant `K + 12`.

This module: Step 1 (generic part) and the generic tools for Steps 2 and 3.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u

/-- `φ (α d) = σ d`. -/
theorem facePerm_alpha_eq_sigma (M : CombMap.{u}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, M.alpha_involutive d]

/-- The face rotation of the dual is the vertex rotation. -/
theorem dual_facePerm_apply_eq (M : CombMap.{u}) (x : M.Dart) :
    M.dual.facePerm x = M.sigma x := by
  rw [CombMap.dual_facePerm]
  rfl

/-- A class step of the dual: the vertex rotation. -/
theorem faceClass_dual_sigma (M : CombMap.{u}) (keep : M.Dart → Prop) (x : M.Dart) :
    Relation.EqvGen (CombMap.FaceClassStep M.dual keep) x (M.sigma x) :=
  Relation.EqvGen.rel _ _ (Or.inl (dual_facePerm_apply_eq M x).symm)

/-- A class step of the dual: crossing a non-retained edge. -/
theorem faceClass_dual_alpha (M : CombMap.{u}) (keep : M.Dart → Prop) {x : M.Dart}
    (hx : ¬ keep x) : Relation.EqvGen (CombMap.FaceClassStep M.dual keep) x (M.alpha x) :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨hx, rfl⟩)

/-- On a non-retained dart, the face rotation of `M` is a class path of the dual. -/
theorem faceClass_dual_facePerm (M : CombMap.{u}) (keep : M.Dart → Prop) {x : M.Dart}
    (hx : ¬ keep x) : Relation.EqvGen (CombMap.FaceClassStep M.dual keep) x (M.facePerm x) := by
  have h := faceClass_dual_sigma M keep (M.alpha x)
  rw [← facePerm_alpha_eq_sigma M (M.alpha x), M.alpha_involutive x] at h
  exact Relation.EqvGen.trans _ _ _ (faceClass_dual_alpha M keep hx) h

/-- **Step 1: a face step of a first-return restriction is a class path.** -/
theorem faceClass_restriction_facePerm (N : CombMap.{u}) (keep : N.Dart → Prop)
    (hkeep : ∀ d, keep (N.alpha d) ↔ keep d)
    (b : (CombMap.PredicateRestriction.toCombMap N keep hkeep).Dart) :
    Relation.EqvGen (CombMap.FaceClassStep N keep) b.1
      ((CombMap.PredicateRestriction.toCombMap N keep hkeep).facePerm b).1 := by
  obtain ⟨m, hm, heq, hskip⟩ := CombMap.PredicateRestriction.sigma_firstReturn N keep
    (CombMap.PredicateRestriction.alpha N keep hkeep b)
  have key : ∀ k, 0 < k → k ≤ m →
      Relation.EqvGen (CombMap.FaceClassStep N keep) b.1 ((N.sigma ^ k) (N.alpha b.1)) := by
    intro k hk hkm
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [zero_add, pow_one]
        exact Relation.EqvGen.rel _ _ (Or.inl rfl)
      · have hy : ¬ keep ((N.sigma ^ k) (N.alpha b.1)) := fun hk' =>
          hskip k hkpos (by omega) ⟨⟨_, hk'⟩, rfl⟩
        have h1 : Relation.EqvGen (CombMap.FaceClassStep N keep) ((N.sigma ^ k) (N.alpha b.1))
            (N.sigma ((N.sigma ^ k) (N.alpha b.1))) :=
          Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨hy, rfl⟩))
            (Relation.EqvGen.rel _ _ (Or.inl (facePerm_alpha_eq_sigma N _).symm))
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (ih hkpos (by omega)) h1
  have h4 : (N.sigma ^ m) (N.alpha b.1) =
      ((CombMap.PredicateRestriction.toCombMap N keep hkeep).facePerm b).1 := heq
  rw [← h4]
  exact key m hm le_rfl

/-- The component relation is invariant under the face rotation. -/
theorem componentOf_facePerm_iff (N : CombMap.{u}) (a z : N.Dart) :
    N.componentOf a (N.facePerm z) ↔ N.componentOf a z := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, N.componentOf_sigma, N.componentOf_alpha]

/-- Darts at one vertex lie in one component. -/
theorem componentOf_of_vertexOf_eq' (N : CombMap.{u}) {a b : N.Dart}
    (h : N.vertexOf a = N.vertexOf b) : N.componentOf a b := by
  have key : ∀ i : ℕ, N.componentOf a ((N.sigma ^ i) a) := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact N.componentOf_self a
    | succ i ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, N.componentOf_sigma]
      exact ih
  obtain ⟨i, hi⟩ := ((N.vertexOf_eq_iff a b).mp h).exists_nat_pow_eq
  rw [← hi]
  exact key i

/-- Darts on one face lie in one component. -/
theorem componentOf_of_faceOf_eq' (N : CombMap.{u}) {a b : N.Dart}
    (h : N.faceOf a = N.faceOf b) : N.componentOf a b := by
  have key : ∀ i : ℕ, N.componentOf a ((N.facePerm ^ i) a) := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact N.componentOf_self a
    | succ i ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, componentOf_facePerm_iff]
      exact ih
  obtain ⟨i, hi⟩ := ((N.faceOf_eq_iff a b).mp h).exists_nat_pow_eq
  rw [← hi]
  exact key i

/-- On a connected map, a predicate closed under `α` and `σ` in both directions is constant. -/
theorem invariant_of_isConnected (N : CombMap.{u}) (hN : N.IsConnected) (B : N.Dart → Prop)
    (hα : ∀ x, B x ↔ B (N.alpha x)) (hσ : ∀ x, B x ↔ B (N.sigma x)) (x y : N.Dart)
    (hx : B x) : B y := by
  have key : ∀ p q, Relation.EqvGen N.Adjacent p q → (B p ↔ B q) := by
    intro p q hpq
    induction hpq with
    | rel p _ h =>
      rcases h with rfl | rfl
      · exact hα p
      · exact hσ p
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key x y (hN x y)).mp hx

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.faceClass_restriction_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.invariant_of_isConnected
