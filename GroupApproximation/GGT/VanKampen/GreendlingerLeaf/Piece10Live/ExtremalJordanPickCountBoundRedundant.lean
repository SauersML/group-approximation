import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSectorNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# One passage per all-free vertex is redundant

Lane gl-p10-42 (the Bound half of `ExtremalJordanPickCountEulerStatement`).  Take a closed walk
`c` that bounds a face set `faces`, a vertex `x` and a relation `R'` containing the face steps
off `c`.  Assume every passage `d → next d` through `x` (that is, with `vertexOf (α d) = x`) has
a free sector, from `next d` to `α d` in the rotation.  Assume also that all of these passages
but one, `d₁ → next d₁`, are `R'`-paths.  Then so is the last one
(`extremalJordanPickCountBound_redundant`).

Proof.  In the walk map `P`, a free sector means `σ_P (next d) = α d`
(`extremalJordanPickCountBound_sigma_eq`).  For every retained dart `z`, `α z` and `σ_P z` share
a face class off `c` (`extremalJordanPickCountBound_faceClass_sigma`).  So `σ_P (α d)` is
`R'`-linked to `d`, and it is a dart of `c`: a face class off `c` stays in `faces`, and the reverse of a dart
of `c` is based outside `faces`.  Walk the `σ_P`-orbit of `x` from `α d₁`, keeping the invariant
`extremalJordanPickCountBound_inv`: the current dart, or its reverse, is a dart of `c` that is
`R'`-linked to `d₁`.  A dart `y` of `c` has `σ_P y = α d` with `next d = y`.  If `d = d₁` we have
linked `d₁` to `next d₁ = y`.  Otherwise the passage `d → y` is an `R'`-path, and `d` is linked to
`d₁`.  The orbit returns to `next d₁`, and the reverse of `next d₁` is not in `c`.  So the first
alternative must have occurred.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u

open SimpleClosedWalkSides

section BoundRedundant

variable (M : CombMap.{u}) (c : List M.Dart)

/-- **Monotonicity of the generated equivalence.** -/
theorem extremalJordanPickCountBound_eqvGen_mono {α : Type*} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {a b : α} (hab : Relation.EqvGen r a b) :
    Relation.EqvGen s a b := by
  induction hab with
  | rel x y hxy => exact Relation.EqvGen.rel x y (h x y hxy)
  | refl x => exact Relation.EqvGen.refl x
  | symm x y _ ih => exact Relation.EqvGen.symm x y ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans x y z ih₁ ih₂

/-- **The orbit invariant**: either the goal `g` holds, or the dart `z` lies at `x` and it, or its
reverse, is a dart of `c` that is `R'`-linked to `d₁`. -/
def extremalJordanPickCountBound_inv (R' : M.Dart → M.Dart → Prop) (g : Prop) (d₁ : M.Dart)
    (x : M.Vertex) (z : (walkMap M c).Dart) : Prop :=
  g ∨ (M.vertexOf z.1 = x ∧ ((z.1 ∈ c ∧ Relation.EqvGen R' d₁ z.1) ∨
    (M.alpha z.1 ∈ c ∧ Relation.EqvGen R' d₁ (M.alpha z.1))))

/-- **The walk rotation keeps the ambient vertex.** -/
theorem extremalJordanPickCountBound_vertexOf_sigma (z : (walkMap M c).Dart) :
    M.vertexOf ((walkMap M c).sigma z).1 = M.vertexOf z.1 :=
  ((walkMap_isRestriction M c).vertexOf_eq_iff _ _).mp ((walkMap M c).vertexOf_sigma z)

/-- **A free sector is one walk rotation step**: `σ_P (next d) = α d`. -/
theorem extremalJordanPickCountBound_sigma_next [DecidableEq M.Dart]
    (hnot : ∀ d ∈ c, M.alpha d ∉ c) (z : (walkMap M c).Dart) {d : M.Dart} (hd : d ∈ c)
    (hz : c.next d hd = z.1)
    (hsf : SectorNoninterleaving.SectorFree M c (c.next d hd) (M.alpha d)) :
    ((walkMap M c).sigma z).1 = M.alpha d := by
  obtain ⟨m, hm, hfree⟩ := hsf
  rw [hz] at hm hfree
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      rw [pow_zero, Equiv.Perm.one_apply] at hm
      have hmem : z.1 ∈ c := by
        rw [← hz]
        exact List.next_mem c d hd
      refine (hnot d hd ?_).elim
      rw [← hm]
      exact hmem
    · exact h0
  have hkeep : walkKeep M c (M.alpha d) := by
    refine Or.inr ?_
    rw [M.alpha_involutive d]
    exact hd
  have := extremalJordanPickCountBound_sigma_eq M c z ⟨M.alpha d, hkeep⟩ m hm0 hm hfree
  rw [this]

/-- **The invariant step** along the walk rotation at the vertex of `α d₁`. -/
theorem extremalJordanPickCountBound_inv_step [DecidableEq M.Dart] (hnodup : c.Nodup)
    (hvn : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (c.next d hd))
    (faces : Finset M.Face)
    (hc : ∀ d, d ∈ c ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces)
    (R' : M.Dart → M.Dart → Prop)
    (hFC : ∀ a b, CombMap.FaceClassStep M (walkKeep M c) a b → R' a b)
    {d₁ : M.Dart} (hd₁ : d₁ ∈ c)
    (hsf : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (M.alpha d₁) →
      SectorNoninterleaving.SectorFree M c (c.next d hd) (M.alpha d))
    (hlink : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (M.alpha d₁) → d ≠ d₁ →
      Relation.EqvGen R' d (c.next d hd))
    (z : (walkMap M c).Dart)
    (hz : extremalJordanPickCountBound_inv M c R' (Relation.EqvGen R' d₁ (c.next d₁ hd₁)) d₁
      (M.vertexOf (M.alpha d₁)) z) :
    extremalJordanPickCountBound_inv M c R' (Relation.EqvGen R' d₁ (c.next d₁ hd₁)) d₁
      (M.vertexOf (M.alpha d₁)) ((walkMap M c).sigma z) := by
  have hnot : ∀ d ∈ c, M.alpha d ∉ c := fun d hd hα => ((hc d).mp hd).2 ((hc _).mp hα).1
  have hvσ := extremalJordanPickCountBound_vertexOf_sigma M c z
  unfold extremalJordanPickCountBound_inv at hz ⊢
  rcases hz with hg | ⟨hvx, ⟨hz, hE⟩ | ⟨hz, hE⟩⟩
  · exact Or.inl hg
  · obtain ⟨d, hd, hnext⟩ : ∃ d, ∃ hd : d ∈ c, c.next d hd = z.1 :=
      ⟨_, List.prev_mem c z.1 hz, List.next_prev c hnodup z.1 hz⟩
    have hdx : M.vertexOf (M.alpha d) = M.vertexOf (M.alpha d₁) := by
      rw [hvn d hd, hnext]
      exact hvx
    have hσ := extremalJordanPickCountBound_sigma_next M c hnot z hd hnext (hsf d hd hdx)
    by_cases hdd : d = d₁
    · subst hdd
      rw [← hnext] at hE
      exact Or.inl hE
    · have hl := hlink d hd hdx hdd
      rw [hnext] at hl
      refine Or.inr ⟨hvσ.trans hvx, Or.inr ⟨?_, ?_⟩⟩
      · rw [hσ, M.alpha_involutive d]
        exact hd
      · rw [hσ, M.alpha_involutive d]
        exact Relation.EqvGen.trans _ _ _ hE (Relation.EqvGen.symm _ _ hl)
  · have hW := extremalJordanPickCountBound_faceClass_sigma M c z
    have hin : M.faceOf ((walkMap M c).sigma z).1 ∈ faces :=
      (extremalJordanPickCountBound_side M c faces hc hW).mp ((hc _).mp hz).1
    have hmem : ((walkMap M c).sigma z).1 ∈ c := by
      rcases ((walkMap M c).sigma z).2 with h | h
      · exact h
      · refine (((hc _).mp h).2 ?_).elim
        rw [M.alpha_involutive]
        exact hin
    exact Or.inr ⟨hvσ.trans hvx, Or.inl ⟨hmem,
      Relation.EqvGen.trans _ _ _ hE (extremalJordanPickCountBound_eqvGen_mono hFC hW)⟩⟩

/-- **The last passage at an all-free vertex is redundant.** -/
theorem extremalJordanPickCountBound_redundant [DecidableEq M.Dart] (hnodup : c.Nodup)
    (hvn : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (c.next d hd))
    (faces : Finset M.Face)
    (hc : ∀ d, d ∈ c ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces)
    (R' : M.Dart → M.Dart → Prop)
    (hFC : ∀ a b, CombMap.FaceClassStep M (walkKeep M c) a b → R' a b)
    {d₁ : M.Dart} (hd₁ : d₁ ∈ c)
    (hsf : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (M.alpha d₁) →
      SectorNoninterleaving.SectorFree M c (c.next d hd) (M.alpha d))
    (hlink : ∀ d (hd : d ∈ c), M.vertexOf (M.alpha d) = M.vertexOf (M.alpha d₁) → d ≠ d₁ →
      Relation.EqvGen R' d (c.next d hd)) :
    Relation.EqvGen R' d₁ (c.next d₁ hd₁) := by
  have hnot : ∀ d ∈ c, M.alpha d ∉ c := fun d hd hα => ((hc d).mp hd).2 ((hc _).mp hα).1
  have hzn : walkKeep M c (c.next d₁ hd₁) := Or.inl (List.next_mem c d₁ hd₁)
  have hσn := extremalJordanPickCountBound_sigma_next M c hnot ⟨_, hzn⟩ hd₁ rfl
    (hsf d₁ hd₁ rfl)
  have base : extremalJordanPickCountBound_inv M c R' (Relation.EqvGen R' d₁ (c.next d₁ hd₁))
      d₁ (M.vertexOf (M.alpha d₁)) ((walkMap M c).sigma ⟨_, hzn⟩) := by
    unfold extremalJordanPickCountBound_inv
    refine Or.inr ⟨by rw [hσn], Or.inr ⟨?_, ?_⟩⟩
    · rw [hσn, M.alpha_involutive d₁]
      exact hd₁
    · rw [hσn, M.alpha_involutive d₁]
      exact Relation.EqvGen.refl d₁
  have hpow : ∀ n : ℕ, extremalJordanPickCountBound_inv M c R'
      (Relation.EqvGen R' d₁ (c.next d₁ hd₁)) d₁ (M.vertexOf (M.alpha d₁))
      (((walkMap M c).sigma ^ n) ((walkMap M c).sigma ⟨_, hzn⟩)) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact base
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact extremalJordanPickCountBound_inv_step M c hnodup hvn faces hc R' hFC hd₁ hsf hlink
        _ ih
  have hcyc : (walkMap M c).sigma.SameCycle ((walkMap M c).sigma ⟨_, hzn⟩) ⟨_, hzn⟩ :=
    Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _)
  obtain ⟨i, hi⟩ := hcyc.exists_nat_pow_eq
  have hfin := hpow i
  rw [hi] at hfin
  unfold extremalJordanPickCountBound_inv at hfin
  rcases hfin with hg | ⟨-, ⟨-, hE⟩ | ⟨hα, -⟩⟩
  · exact hg
  · exact hE
  · exact (hnot _ (List.next_mem c d₁ hd₁) hα).elim

end BoundRedundant

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_eqvGen_mono
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_inv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_vertexOf_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_sigma_next
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_inv_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_redundant
