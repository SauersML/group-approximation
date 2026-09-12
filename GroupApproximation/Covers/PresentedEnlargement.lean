import GroupApproximation.Covers.KazhdanCover

/-!
# Enlarging the relator set of a presented group

Imposing extra relators on a presentation is a quotient map.  This file
isolates that observation from the inline use inside
`exists_kazhdan_finitelyPresented_cover_of_not_isSofic`
(`GroupApproximation/Covers/KazhdanCover.lean`), where the transported
Shalom relators `relsP` were enlarged to `relsH = relsP ∪ (table family)`
by hand.

Three generic facts, for `rels ⊆ rels'` inside `FreeGroup ι`:

* `PresentedEnlargement.enlarge` -- the canonical map
  `PresentedGroup rels →* PresentedGroup rels'` fixing the generators, with
  its computation rule `enlarge_mk` and its surjectivity;
* `PresentedEnlargement.hasKazhdanPropertyT_of_subset` -- property `(T)`
  travels along it, since a quotient of a Kazhdan group is Kazhdan.  Both
  presented groups live in the universe of the generating type, so no
  universe descent is involved: the group universe is literally unchanged;
* `PresentedEnlargement.factor` -- a free-group homomorphism killing every
  relator descends to the presented group, with computation rule
  `factor_mk`.

Nothing here mentions a particular generating type, so the same three facts
serve a `Fin n` cover and a two-block cover over a sum alphabet.  The
Hilbert-hotel consumers live in
`GroupApproximation/Leavitt/HilbertHotelCoverDischarges.lean`; this file
stays free of `Leavitt` imports.
-/

namespace GroupApproximation

namespace PresentedEnlargement

universe u v w

variable {ι : Type u} {rels rels' : Set (FreeGroup ι)}
variable {H : Type v} [Group H]

/-! ## Free lifts of the two canonical generator maps -/

/-- Lifting the generators of a presented group to their own classes is the
quotient map. -/
theorem lift_of_eq_mk (S : Set (FreeGroup ι)) :
    ∀ w : FreeGroup ι,
      FreeGroup.lift (fun i ↦ (PresentedGroup.of i : PresentedGroup S)) w =
        PresentedGroup.mk S w :=
  freeGroup_hom_eq_on fun i ↦ by
    rw [FreeGroup.lift_apply_of]
    rfl

/-- A homomorphism out of a free group is the lift of its own restriction to
the generators. -/
theorem lift_comp_of (f : FreeGroup ι →* H) :
    ∀ w : FreeGroup ι, FreeGroup.lift (fun i ↦ f (FreeGroup.of i)) w = f w :=
  freeGroup_hom_eq_on fun i ↦ by rw [FreeGroup.lift_apply_of]

/-! ## The enlargement homomorphism -/

/-- An old relator dies in the enlarged presented group, which is what makes
the generator-to-generator map well defined. -/
theorem lift_of_subset_eq_one (h : rels ⊆ rels') :
    ∀ r ∈ rels,
      FreeGroup.lift (fun i ↦ (PresentedGroup.of i : PresentedGroup rels')) r = 1 :=
  fun r hr ↦ (lift_of_eq_mk rels' r).trans (PresentedGroup.one_of_mem (h hr))

/-- **Relator enlargement.**  Imposing more relators on the same generators
gives a canonical homomorphism of presented groups. -/
noncomputable def enlarge (h : rels ⊆ rels') :
    PresentedGroup rels →* PresentedGroup rels' :=
  PresentedGroup.toGroup (lift_of_subset_eq_one h)

/-- The enlargement computes on classes: it is the identity on words. -/
theorem enlarge_mk (h : rels ⊆ rels') (w : FreeGroup ι) :
    enlarge h (PresentedGroup.mk rels w) = PresentedGroup.mk rels' w := by
  refine Eq.trans ?_ (lift_of_eq_mk rels' w)
  exact presentedGroup_toGroup_mk (lift_of_subset_eq_one h) w

/-- The enlargement fixes the generators. -/
theorem enlarge_of (h : rels ⊆ rels') (i : ι) :
    enlarge h (PresentedGroup.of i) = (PresentedGroup.of i : PresentedGroup rels') :=
  enlarge_mk h (FreeGroup.of i)

/-- The enlargement is onto: the enlarged group has the same generators. -/
theorem enlarge_surjective (h : rels ⊆ rels') :
    Function.Surjective (enlarge h) := by
  intro γ
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective rels' γ
  exact ⟨PresentedGroup.mk rels w, enlarge_mk h w⟩

/-- **Property `(T)` transfer.**  Enlarging the relator set of a Kazhdan
presented group keeps property `(T)`, the enlargement being onto.  Both
presented groups live in the universe of the generating type, so the group
universe is unchanged; the representation universe `w` is untouched. -/
theorem hasKazhdanPropertyT_of_subset (h : rels ⊆ rels')
    (hT : HasKazhdanPropertyT.{u, w} (PresentedGroup rels)) :
    HasKazhdanPropertyT.{u, w} (PresentedGroup rels') :=
  HasKazhdanPropertyT.of_surjective (enlarge h) (enlarge_surjective h) hT

/-! ## Factoring a free homomorphism through a presentation -/

/-- **The factoring homomorphism.**  A homomorphism out of the free group
that kills every relator descends to the presented group.  This is
`PresentedGroup.toGroup` phrased for a homomorphism rather than a bare
generator map. -/
noncomputable def factor (f : FreeGroup ι →* H) (hf : ∀ r ∈ rels, f r = 1) :
    PresentedGroup rels →* H :=
  PresentedGroup.toGroup (f := fun i ↦ f (FreeGroup.of i))
    (fun r hr ↦ (lift_comp_of f r).trans (hf r hr))

/-- The factoring homomorphism computes on classes. -/
theorem factor_mk (f : FreeGroup ι →* H) (hf : ∀ r ∈ rels, f r = 1)
    (w : FreeGroup ι) : factor f hf (PresentedGroup.mk rels w) = f w := by
  refine Eq.trans ?_ (lift_comp_of f w)
  exact presentedGroup_toGroup_mk
    (fun r hr ↦ (lift_comp_of f r).trans (hf r hr)) w

/-- The factoring homomorphism inherits surjectivity. -/
theorem factor_surjective (f : FreeGroup ι →* H) (hf : ∀ r ∈ rels, f r = 1)
    (hsurj : Function.Surjective f) : Function.Surjective (factor f hf) := by
  intro x
  obtain ⟨w, rfl⟩ := hsurj x
  exact ⟨PresentedGroup.mk rels w, factor_mk f hf w⟩

end PresentedEnlargement

end GroupApproximation
