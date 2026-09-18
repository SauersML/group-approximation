import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk map of a boundary walk: rotation, face classes, darts

Lane gl-p10-42 (the Bound half of `ExtremalJordanPickCountEulerStatement`).  Generic facts on the
walk map `P = walkMap M c` of a dart list `c`, whose darts are the darts of `c` and their reverses.

* `extremalJordanPickCountBound_sigma_eq`.  If `σ^m z = y` for some `m > 0` with no retained dart
  strictly between, then `σ_P z = y`.  Proof: the first return time `m'` of `z` is neither `< m`
  (then `σ^{m'} z` would be a retained dart before `y`) nor `> m` (then `y` would be a retained
  dart before the return); so `m = m'`.
* `extremalJordanPickCountBound_faceClass_sigma`.  `α z` and `σ_P z` lie in one face class
  off `c`: from `α z`, the face steps `x ↦ σ (α x)` and reversals of unretained darts run
  along the ambient rotation from `z` to its first return.
* `extremalJordanPickCountBound_two_mul_card_le`.  If `c` meets no reverse of its own darts, then
  `P` has at least `2 * #c` darts.
* `extremalJordanPickCountBound_side`.  When `c` is the boundary of a face set `faces`, a face
  class off `c` does not cross from `faces` to its complement: the only crossing moves are
  reversals of unretained darts, and an unretained dart lies on one side with its reverse.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u

open SimpleClosedWalkSides

section BoundWalk

variable (M : CombMap.{u}) (c : List M.Dart)

/-- **The walk rotation is the first free return.** -/
theorem extremalJordanPickCountBound_sigma_eq (z y : (walkMap M c).Dart) (m : ℕ) (hm : 0 < m)
    (hmy : (M.sigma ^ m) z.1 = y.1)
    (hfree : ∀ k, 0 < k → k < m → ¬walkKeep M c ((M.sigma ^ k) z.1)) :
    (walkMap M c).sigma z = y := by
  obtain ⟨m', hm'0, hm', hfree'⟩ := (walkMap_isRestriction M c).sigma_firstReturn z
  have hm'' : (M.sigma ^ m') z.1 = ((walkMap M c).sigma z).1 := hm'
  rcases lt_trichotomy m m' with hlt | rfl | hgt
  · exact (hfree' m hm hlt ⟨y, hmy.symm⟩).elim
  · exact Subtype.ext (hm''.symm.trans hmy)
  · have hk : walkKeep M c ((M.sigma ^ m') z.1) := by
      rw [hm'']
      exact ((walkMap M c).sigma z).2
    exact (hfree m' hm'0 hgt hk).elim

/-- **The reverse of a walk dart and its walk rotation share a face class.** -/
theorem extremalJordanPickCountBound_faceClass_sigma (z : (walkMap M c).Dart) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha z.1)
      ((walkMap M c).sigma z).1 := by
  obtain ⟨m, hm0, hm, hfree⟩ := (walkMap_isRestriction M c).sigma_firstReturn z
  have hm' : (M.sigma ^ m) (M.alpha (M.alpha z.1)) = ((walkMap M c).sigma z).1 := by
    rw [M.alpha_involutive z.1]
    exact hm
  have hrun := faceClass_run M (walkKeep M c) (M.alpha z.1) m (fun k hk hkm hkeep => by
    rw [M.alpha_involutive z.1] at hkeep
    exact hfree k hk hkm ⟨⟨_, hkeep⟩, rfl⟩) m hm0 le_rfl
  rw [hm'] at hrun
  exact hrun

/-- **Darts of the walk map**: a list disjoint from its reverses gives at least `2 * #c` darts. -/
theorem extremalJordanPickCountBound_two_mul_card_le (B : Finset M.Dart)
    (hB : ∀ d, d ∈ B ↔ d ∈ c) (hdisj : ∀ d ∈ c, M.alpha d ∉ c) :
    2 * B.card ≤ (walkMap M c).dartCount := by
  classical
  have hd : Disjoint B (B.image M.alpha) := by
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    exact hdisj b ((hB b).mp hb) ((hB _).mp ha)
  have hcard : (B ∪ B.image M.alpha).card = 2 * B.card := by
    rw [Finset.card_union_eq_card_add_card.mpr hd,
      Finset.card_image_of_injective _ M.alpha.injective]
    omega
  have hkeep : ∀ x ∈ B ∪ B.image M.alpha, walkKeep M c x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl ((hB x).mp hx)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      refine Or.inr ?_
      rw [M.alpha_involutive b]
      exact (hB b).mp hb
  let f : (B ∪ B.image M.alpha : Finset M.Dart) → (walkMap M c).Dart :=
    fun x => ⟨x.1, hkeep x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h' : (f x).1 = (f y).1 := by rw [hxy]
    exact Subtype.ext h'
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard, hcard] at hle
  exact hle

/-- **Face classes off a boundary stay on one side.** -/
theorem extremalJordanPickCountBound_side (faces : Finset M.Face)
    (hc : ∀ d, d ∈ c ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces) {a b : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) a b) :
    (M.faceOf a ∈ faces ↔ M.faceOf b ∈ faces) := by
  induction h with
  | rel x y hxy =>
    rcases hxy with rfl | ⟨hk, rfl⟩
    · rw [M.faceOf_facePerm]
    · constructor
      · intro hx
        by_contra hy
        exact hk (Or.inl ((hc x).mpr ⟨hx, hy⟩))
      · intro hy
        by_contra hx
        refine hk (Or.inr ((hc (M.alpha x)).mpr ⟨hy, ?_⟩))
        rw [M.alpha_involutive x]
        exact hx
  | refl => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end BoundWalk

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_sigma_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_faceClass_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_two_mul_card_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_side
