import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Class counts under added relation steps

Lane gl-p10-42 (the Bound half of `ExtremalJordanPickCountEulerStatement`).  Generic
union-find facts used by the count of linked classes.

* `extremalJordanPickCountBound_card_mono`.  If every `R₁`-step is an `R₂`-path, the finset of
  `R₂`-classes of `B` has at most as many elements as that of `R₁`-classes.
* `extremalJordanPickCountBound_card_pair`.  Adding one symmetric pair `a ~ b` to a relation
  lowers the number of classes of `B` by at most one.  Proof: send an `R`-class to its
  `R'`-class.  On the `R`-classes other than that of `a` this map is injective, because an
  `R'`-path either avoids the new pair (so it is an `R`-path), or passes it once, and then one
  endpoint is `R`-linked to `a`.
* `extremalJordanPickCountBound_card_steps`.  Adding the steps `x → f x` for `x ∈ S` lowers the
  number of classes by at most `#S`.  Induction on `S`, one pair at a time.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

open scoped Classical

/-- **Coarser relations have fewer classes.** -/
theorem extremalJordanPickCountBound_card_mono {α : Type*} {R₁ R₂ : α → α → Prop}
    (h : ∀ x y, R₁ x y → Relation.EqvGen R₂ x y) (B : Finset α) :
    (B.image (Quot.mk R₂)).card ≤ (B.image (Quot.mk R₁)).card := by
  let g : Quot R₁ → Quot R₂ :=
    Quot.lift (Quot.mk R₂) fun x y hxy => Quot.eqvGen_sound (h x y hxy)
  have himg : (B.image (Quot.mk R₁)).image g = B.image (Quot.mk R₂) := by
    rw [Finset.image_image]
    rfl
  rw [← himg]
  exact Finset.card_image_le

/-- **One added pair merges at most two classes.** -/
theorem extremalJordanPickCountBound_card_pair {α : Type*} {R R' : α → α → Prop} (a b : α)
    (h₁ : ∀ x y, R x y → R' x y)
    (h₂ : ∀ x y, R' x y → R x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) (B : Finset α) :
    (B.image (Quot.mk R)).card ≤ (B.image (Quot.mk R')).card + 1 := by
  let g : Quot R → Quot R' := Quot.lift (Quot.mk R') fun x y hxy => Quot.sound (h₁ x y hxy)
  have hmaps : Set.MapsTo g ((B.image (Quot.mk R)).erase (Quot.mk R a) : Set (Quot R))
      (B.image (Quot.mk R') : Set (Quot R')) := by
    intro q hq
    obtain ⟨-, hq⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hq)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hinj : Set.InjOn g ((B.image (Quot.mk R)).erase (Quot.mk R a) : Set (Quot R)) := by
    intro q hq q' hq' hgq
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hq)
    obtain ⟨hne', hq'⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hq')
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hq'
    have hgq' : Quot.mk R' x = Quot.mk R' y := hgq
    have hxy : Relation.EqvGen R' x y := Quot.eqvGen_exact hgq'
    rcases CombMap.eqvGen_cases_of_pair h₂ hxy with h | ⟨h, -⟩ | ⟨-, h⟩
    · exact Quot.eqvGen_sound h
    · exact absurd (Quot.eqvGen_sound h) hne
    · exact absurd (Quot.eqvGen_sound h.symm) hne'
  have hle := Finset.card_le_card_of_injOn g hmaps hinj
  have hpred := Finset.pred_card_le_card_erase (s := B.image (Quot.mk R)) (a := Quot.mk R a)
  omega

/-- **Added steps `x → f x` for `x ∈ S` merge at most `#S` classes.** -/
theorem extremalJordanPickCountBound_card_steps {α : Type*} (R : α → α → Prop) (f : α → α)
    (B S : Finset α) :
    (B.image (Quot.mk R)).card ≤
      (B.image (Quot.mk fun x y => R x y ∨ (x ∈ S ∧ y = f x))).card + S.card := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty, Nat.add_zero]
    refine extremalJordanPickCountBound_card_mono ?_ B
    intro x y h
    rcases h with h | ⟨h, -⟩
    · exact Relation.EqvGen.rel _ _ h
    · exact absurd h (Finset.notMem_empty x)
  | insert s₀ S hs ih =>
    have hpair := extremalJordanPickCountBound_card_pair
      (R := fun x y => R x y ∨ (x ∈ S ∧ y = f x))
      (R' := fun x y => (R x y ∨ (x ∈ S ∧ y = f x)) ∨ (x = s₀ ∧ y = f s₀)) s₀ (f s₀)
      (fun x y h => Or.inl h)
      (fun x y h => by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) B
    have hrel : ∀ x y, (R x y ∨ (x ∈ insert s₀ S ∧ y = f x)) →
        Relation.EqvGen (fun x y => (R x y ∨ (x ∈ S ∧ y = f x)) ∨ (x = s₀ ∧ y = f s₀)) x y := by
      intro x y h
      refine Relation.EqvGen.rel _ _ ?_
      rcases h with h | ⟨hx, rfl⟩
      · exact Or.inl (Or.inl h)
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl (Or.inr ⟨hx, rfl⟩)
    have hmono := extremalJordanPickCountBound_card_mono hrel B
    rw [Finset.card_insert_of_notMem hs]
    omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_card_mono
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_card_pair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_card_steps
