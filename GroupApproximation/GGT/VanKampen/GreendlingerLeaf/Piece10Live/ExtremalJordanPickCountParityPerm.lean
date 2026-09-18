import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The parity clause: the face permutation `α ∘ σ_P` on the walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-43.

Let `c` be the walk and `σ_P` the rotation of the walk map `P`: the first return of `σ` to the
darts kept by `walkKeep c`.  This file builds the permutation

  `extremalJordanPickCountParity_perm K`:  `d ↦ α (σ_P d)` for `d ∈ c`, and `d ↦ d` off `c`.

It maps walk darts to walk darts.  By the proved alternation fact, the first kept dart after a walk
dart is a reversal `α e` with `e ∈ c`.  So it is well defined and injective, hence a permutation.

**The first-passage law** (`extremalJordanPickCountParity_perm_next_iff`): for `d ∈ c`,

  `perm (next d) = d  ↔  d is a first passage`.

Both sides say that `α d` is the first kept dart after `next d` in the rotation
(`FirstTurn.reverse_map_alpha_iff`).  This is exactly the hypothesis `hfirst` of
`extremalJordanPickCountParity_of_perm`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section ParityPerm

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The face step on the walk**: `d ↦ α (σ_P d)` on walk darts, the identity elsewhere. -/
noncomputable def extremalJordanPickCountParity_fun (K : PocketFaceSet D eps X lo hi)
    (d : X.toCombMap.Dart) : X.toCombMap.Dart :=
  if hd : d ∈ K.boundary.cycle then
    X.toCombMap.alpha (CombMap.PredicateRestriction.sigma X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) ⟨d, Or.inl hd⟩).1
  else d

/-- The face step at a walk dart. -/
theorem extremalJordanPickCountParity_fun_of_mem (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    extremalJordanPickCountParity_fun K d =
      X.toCombMap.alpha (CombMap.PredicateRestriction.sigma X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle) ⟨d, Or.inl hd⟩).1 := by
  unfold extremalJordanPickCountParity_fun
  exact dif_pos hd

/-- The face step off the walk is the identity. -/
theorem extremalJordanPickCountParity_fun_of_not_mem (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∉ K.boundary.cycle) :
    extremalJordanPickCountParity_fun K d = d := by
  unfold extremalJordanPickCountParity_fun
  exact dif_neg hd

/-- **The rotation of the walk map is a first return**: `σ_P d = σ^m d` for some `m > 0`, and no
dart strictly between is kept. -/
theorem extremalJordanPickCountParity_sigma_spec (K : PocketFaceSet D eps X lo hi)
    (d : X.toCombMap.Dart) (hd : walkKeep X.toCombMap K.boundary.cycle d) :
    ∃ m : ℕ, 0 < m ∧
      (X.toCombMap.sigma ^ m) d = (CombMap.PredicateRestriction.sigma X.toCombMap
        (walkKeep X.toCombMap K.boundary.cycle) ⟨d, hd⟩).1 ∧
      ∀ t, 0 < t → t < m →
        ¬walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) d) := by
  obtain ⟨m, hm, hpm, hav⟩ := CombMap.PredicateRestriction.sigma_firstReturn X.toCombMap
    (walkKeep X.toCombMap K.boundary.cycle) ⟨d, hd⟩
  exact ⟨m, hm, hpm, fun t ht htm hk => hav t ht htm ⟨⟨(X.toCombMap.sigma ^ t) d, hk⟩, rfl⟩⟩

/-- **The face step stays on the walk**: by alternation, the first kept dart after a walk dart
is the reversal of a walk dart. -/
theorem extremalJordanPickCountParity_alpha_sigma_mem (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    X.toCombMap.alpha (CombMap.PredicateRestriction.sigma X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) ⟨d, Or.inl hd⟩).1 ∈ K.boundary.cycle := by
  obtain ⟨m, hm, hpm, hfree⟩ := extremalJordanPickCountParity_sigma_spec K d (Or.inl hd)
  have hk : walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ m) d) := by
    rw [hpm]
    exact (CombMap.PredicateRestriction.sigma X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle) ⟨d, Or.inl hd⟩).2
  have h := extremalJordanPickEuler_alternates K d hd m hm hfree hk
  rwa [hpm] at h

/-- The face step is injective. -/
theorem extremalJordanPickCountParity_fun_injective (K : PocketFaceSet D eps X lo hi) :
    Function.Injective (extremalJordanPickCountParity_fun K) := by
  intro d d' h
  by_cases hd : d ∈ K.boundary.cycle <;> by_cases hd' : d' ∈ K.boundary.cycle
  · rw [extremalJordanPickCountParity_fun_of_mem K hd,
      extremalJordanPickCountParity_fun_of_mem K hd'] at h
    have h1 := X.toCombMap.alpha.injective h
    have h2 := (CombMap.PredicateRestriction.sigma X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)).injective (Subtype.ext h1)
    exact congrArg Subtype.val h2
  · rw [extremalJordanPickCountParity_fun_of_mem K hd,
      extremalJordanPickCountParity_fun_of_not_mem K hd'] at h
    exact absurd (by rw [← h]; exact extremalJordanPickCountParity_alpha_sigma_mem K hd) hd'
  · rw [extremalJordanPickCountParity_fun_of_not_mem K hd,
      extremalJordanPickCountParity_fun_of_mem K hd'] at h
    exact absurd (by rw [h]; exact extremalJordanPickCountParity_alpha_sigma_mem K hd') hd
  · rw [extremalJordanPickCountParity_fun_of_not_mem K hd,
      extremalJordanPickCountParity_fun_of_not_mem K hd'] at h
    exact h

/-- **The face permutation on the walk**: `α ∘ σ_P` on walk darts, the identity elsewhere. -/
noncomputable def extremalJordanPickCountParity_perm (K : PocketFaceSet D eps X lo hi) :
    Equiv.Perm X.toCombMap.Dart :=
  Equiv.ofBijective (extremalJordanPickCountParity_fun K)
    (Finite.injective_iff_bijective.mp (extremalJordanPickCountParity_fun_injective K))

/-- The face permutation applies the face step. -/
theorem extremalJordanPickCountParity_perm_apply (K : PocketFaceSet D eps X lo hi)
    (d : X.toCombMap.Dart) :
    extremalJordanPickCountParity_perm K d = extremalJordanPickCountParity_fun K d :=
  rfl

/-- The face permutation fixes the darts off the walk. -/
theorem extremalJordanPickCountParity_perm_of_not_mem (K : PocketFaceSet D eps X lo hi) :
    ∀ d, d ∉ K.boundary.cycle → extremalJordanPickCountParity_perm K d = d := fun d hd => by
  rw [extremalJordanPickCountParity_perm_apply]
  exact extremalJordanPickCountParity_fun_of_not_mem K hd

/-- **The first-passage law for the face step**: `f (next d) = d` exactly when `d` is a first
passage.  Both say that `α d` is the first kept dart after `next d` in the rotation. -/
theorem extremalJordanPickCountParity_fun_next_iff (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    extremalJordanPickCountParity_fun K (K.boundary.cycle.next d hd) = d ↔
      ¬P10ChordLift.NonFirstTurn K d hd := by
  have he : K.boundary.cycle.next d hd ∈ K.boundary.cycle := List.next_mem _ _ hd
  obtain ⟨m, hm, hpm, hfree⟩ :=
    extremalJordanPickCountParity_sigma_spec K (K.boundary.cycle.next d hd) (Or.inl he)
  have hkd : walkKeep X.toCombMap K.boundary.cycle (X.toCombMap.alpha d) :=
    (walkKeep_alpha X.toCombMap K.boundary.cycle d).mpr (Or.inl hd)
  rw [extremalJordanPickCountParity_fun_of_mem K he]
  unfold P10ChordLift.NonFirstTurn
  rw [not_not, FirstTurn.reverse_map_alpha_iff]
  constructor
  · intro h
    refine ⟨m, hm, ?_, hfree⟩
    rw [hpm]
    apply X.toCombMap.alpha.injective
    rw [X.toCombMap.alpha_involutive d]
    exact h
  · rintro ⟨k, hk, hke, hkfree⟩
    have hkm : k = m := by
      rcases lt_trichotomy k m with hlt | heq | hgt
      · exact (hfree k hk hlt (by rw [hke]; exact hkd)).elim
      · exact heq
      · refine (hkfree m hm hgt ?_).elim
        rw [hpm]
        exact (CombMap.PredicateRestriction.sigma X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle) ⟨K.boundary.cycle.next d hd, Or.inl he⟩).2
    rw [hkm] at hke
    rw [← hpm, hke, X.toCombMap.alpha_involutive d]

/-- **The first-passage law**: `perm (next d) = d` exactly when `d` is a first passage. -/
theorem extremalJordanPickCountParity_perm_next_iff (K : PocketFaceSet D eps X lo hi) :
    ∀ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle),
      extremalJordanPickCountParity_perm K (K.boundary.cycle.next d hd) = d ↔
        ¬P10ChordLift.NonFirstTurn K d hd := fun d hd => by
  rw [extremalJordanPickCountParity_perm_apply]
  exact extremalJordanPickCountParity_fun_next_iff K hd

end ParityPerm

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_fun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_fun_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_fun_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_sigma_spec
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_alpha_sigma_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_fun_injective
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_perm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_perm_apply
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_perm_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_fun_next_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_perm_next_iff
