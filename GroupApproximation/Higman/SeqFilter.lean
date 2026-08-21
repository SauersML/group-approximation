import GroupApproximation.Higman.CoordCalculus

/-!
# Filtering a coded sequence

Higman's operations `ζ`, `π` and `ωₘ` all say the same kind of thing: two
sequences are related when they **agree on a set of coordinates** and are
unconstrained off it.  On the group side the coded sequence

    elt f = ∏ᵢ (of i) ^ f i        (the product over the support, increasing)

has to be split accordingly, and the two halves have to be recognizable from
each other.  This file supplies both, and nothing else in the operation
closures touches the sorted-list definition of `elt`.

The one fact that makes it work is that `elt` does not care which enumerating
list is used, as long as it is sorted, repetition-free and covers the support:
`elt_eq_eltOn`.  Zero exponents contribute `1`, so a longer list is harmless,
and a sorted repetition-free list is determined by the finite set underlying
it (`List.toFinset_sort`).  With that, *filtering* the sequence is *filtering*
the list, and:

* `killOn p` --- the retraction of `FreeGroup ℤ` deleting the generators
  outside `p` --- computes the filtered sequence: `killOn_elt`,

      killOn p (elt f) = elt (Finsupp.filter p f) ,

  which with `elt_injective` turns "the coded sequences differ by something
  supported off `p`" into "the sequences agree on `p`".  That is the
  reverse inclusion of every one of the three operation identities.
* `elt_split` --- the coded sequence factors at any threshold `k`,

      elt f = elt (f restricted to i ≤ k) * elt (f restricted to i > k) ,

  because a sorted list splits as its two filters at a threshold.  That is the
  forward inclusion.

Both are stated on `FreeGroup ℤ`, before the row coding `rowHom` carries them
into `F₃`; `rowHom` is injective (`Seq.rowHom_injective`), so nothing is lost.
-/

namespace GroupApproximation
namespace Higman
namespace Split

open GroupApproximation.Higman.Seq

/-! ## 1.  The coding along an explicit list -/

/-- The coded product along an explicit list of indices. -/
noncomputable def eltOn (L : List ℤ) (f : E) : FreeGroup ℤ :=
  (L.map fun i => FreeGroup.of i ^ f i).prod

@[simp] theorem eltOn_nil (f : E) : eltOn [] f = 1 := rfl

@[simp] theorem eltOn_cons (i : ℤ) (L : List ℤ) (f : E) :
    eltOn (i :: L) f = FreeGroup.of i ^ f i * eltOn L f := rfl

theorem eltOn_append (L M : List ℤ) (f : E) :
    eltOn (L ++ M) f = eltOn L f * eltOn M f := by
  unfold eltOn
  rw [List.map_append, List.prod_append]

theorem eltOn_congr {L : List ℤ} {f g : E} (h : ∀ i ∈ L, f i = g i) :
    eltOn L f = eltOn L g := by
  unfold eltOn
  refine congrArg List.prod ?_
  exact List.map_congr_left fun i hi => by rw [h i hi]

theorem elt_eq_eltOn_support (f : E) : elt f = eltOn (f.support.sort (· ≤ ·)) f := rfl

/-! ## 2.  Zero exponents may be dropped -/

theorem eltOn_filter_support (L : List ℤ) (f : E) :
    eltOn (L.filter (fun i => decide (f i ≠ 0))) f = eltOn L f := by
  induction L with
  | nil => rfl
  | cons i M ih =>
      by_cases hi : f i = 0
      · have hfil : (i :: M).filter (fun j => decide (f j ≠ 0))
            = M.filter (fun j => decide (f j ≠ 0)) := by
          rw [List.filter_cons]
          simp [hi]
        rw [hfil, ih, eltOn_cons, hi, zpow_zero, one_mul]
      · have hfil : (i :: M).filter (fun j => decide (f j ≠ 0))
            = i :: M.filter (fun j => decide (f j ≠ 0)) := by
          rw [List.filter_cons]
          simp [hi]
        rw [hfil, eltOn_cons, eltOn_cons, ih]

/-! ## 3.  The coding does not depend on the enumerating list -/

/-- **Any sorted repetition-free list covering the support computes `elt`.** -/
theorem elt_eq_eltOn {L : List ℤ} {f : E} (hpair : L.Pairwise (· ≤ ·))
    (hnodup : L.Nodup) (hsub : ∀ i ∈ f.support, i ∈ L) : elt f = eltOn L f := by
  classical
  have hnodup' : (L.filter (fun i => decide (f i ≠ 0))).Nodup := hnodup.filter _
  have hpair' : (L.filter (fun i => decide (f i ≠ 0))).Pairwise (· ≤ ·) :=
    hpair.filter _
  have hto : (L.filter (fun i => decide (f i ≠ 0))).toFinset = f.support := by
    ext i
    constructor
    · intro hi
      rw [List.mem_toFinset, List.mem_filter] at hi
      exact Finsupp.mem_support_iff.mpr (by simpa using hi.2)
    · intro hi
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨hsub i hi, by simpa using Finsupp.mem_support_iff.mp hi⟩
  have hsort : f.support.sort (· ≤ ·) = L.filter (fun i => decide (f i ≠ 0)) := by
    rw [← hto]
    exact (List.toFinset_sort (· ≤ ·) hnodup').mpr hpair'
  rw [elt_eq_eltOn_support, hsort, eltOn_filter_support]

/-! ## 4.  Filtering -/

theorem elt_filter {p : ℤ → Prop} [DecidablePred p] (f : E) :
    elt (Finsupp.filter p f)
      = eltOn ((f.support.sort (· ≤ ·)).filter (fun i => decide (p i))) f := by
  classical
  have hL : ((f.support.sort (· ≤ ·)).filter (fun i => decide (p i))).Pairwise (· ≤ ·) :=
    (Finset.pairwise_sort _ _).filter _
  have hN : ((f.support.sort (· ≤ ·)).filter (fun i => decide (p i))).Nodup :=
    (Finset.sort_nodup _ _).filter _
  have hsub : ∀ i ∈ (Finsupp.filter p f).support,
      i ∈ (f.support.sort (· ≤ ·)).filter (fun i => decide (p i)) := by
    intro i hi
    rw [Finsupp.support_filter, Finset.mem_filter] at hi
    refine List.mem_filter.mpr ⟨?_, by simpa using hi.2⟩
    rw [Finset.mem_sort]
    exact hi.1
  rw [elt_eq_eltOn hL hN hsub]
  refine eltOn_congr fun i hi => ?_
  have hp : p i := by simpa using (List.mem_filter.mp hi).2
  rw [Finsupp.filter_apply, if_pos hp]

/-! ## 5.  The retraction deleting the generators outside a set -/

/-- Delete the generators whose index fails `p`. -/
def killOn (p : ℤ → Prop) [DecidablePred p] : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => if p i then FreeGroup.of i else 1)

@[simp] theorem killOn_of (p : ℤ → Prop) [DecidablePred p] (i : ℤ) :
    killOn p (FreeGroup.of i) = if p i then FreeGroup.of i else 1 := by
  unfold killOn
  rw [FreeGroup.lift_apply_of]

theorem killOn_eltOn (p : ℤ → Prop) [DecidablePred p] (L : List ℤ) (f : E) :
    killOn p (eltOn L f) = eltOn (L.filter (fun i => decide (p i))) f := by
  induction L with
  | nil =>
      rw [eltOn_nil, map_one]
      rfl
  | cons i M ih =>
      by_cases hi : p i
      · have hfil : (i :: M).filter (fun j => decide (p j))
            = i :: M.filter (fun j => decide (p j)) := by
          rw [List.filter_cons]
          simp [hi]
        rw [hfil, eltOn_cons, eltOn_cons, map_mul, ih, map_zpow, killOn_of, if_pos hi]
      · have hfil : (i :: M).filter (fun j => decide (p j))
            = M.filter (fun j => decide (p j)) := by
          rw [List.filter_cons]
          simp [hi]
        rw [hfil, eltOn_cons, map_mul, ih, map_zpow, killOn_of, if_neg hi, one_zpow, one_mul]

/-- **The deletion retraction computes the filtered sequence.** -/
theorem killOn_elt (p : ℤ → Prop) [DecidablePred p] (f : E) :
    killOn p (elt f) = elt (Finsupp.filter p f) := by
  rw [elt_eq_eltOn_support, killOn_eltOn, elt_filter]

/-- The generators outside `p` die. -/
theorem killOn_eq_one_of_mem_closure {p : ℤ → Prop} [DecidablePred p]
    {w : FreeGroup ℤ} (hw : w ∈ Subgroup.closure (FreeGroup.of '' {i : ℤ | ¬ p i})) :
    killOn p w = 1 := by
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [killOn_of, if_neg hi]
  | one => exact map_one _
  | mul y z _ _ ihy ihz => rw [map_mul, ihy, ihz, one_mul]
  | inv y _ ihy => rw [map_inv, ihy, inv_one]

/-! ## 6.  Splitting at a threshold -/

theorem list_split_of_pairwise {L : List ℤ} (k : ℤ) (hpair : L.Pairwise (· ≤ ·)) :
    L = L.filter (fun i => decide (i ≤ k)) ++ L.filter (fun i => decide (¬ i ≤ k)) := by
  induction L with
  | nil => rfl
  | cons i M ih =>
      rw [List.pairwise_cons] at hpair
      by_cases hi : i ≤ k
      · have h1 : (i :: M).filter (fun j => decide (j ≤ k))
            = i :: M.filter (fun j => decide (j ≤ k)) := by
          rw [List.filter_cons, if_pos (by simpa using hi)]
        have h2 : (i :: M).filter (fun j => decide (¬ j ≤ k))
            = M.filter (fun j => decide (¬ j ≤ k)) := by
          rw [List.filter_cons, if_neg (by simpa using hi)]
        rw [h1, h2, List.cons_append, ← ih hpair.2]
      · have hall : ∀ j ∈ M, ¬ j ≤ k := fun j hj hle => hi (le_trans (hpair.1 j hj) hle)
        have hM1 : M.filter (fun j => decide (j ≤ k)) = [] :=
          List.filter_eq_nil_iff.mpr fun j hj => by simpa using hall j hj
        have hM2 : M.filter (fun j => decide (¬ j ≤ k)) = M :=
          List.filter_eq_self.mpr fun j hj => by simpa using hall j hj
        have h1 : (i :: M).filter (fun j => decide (j ≤ k)) = [] := by
          rw [List.filter_cons, if_neg (by simpa using hi), hM1]
        have h2 : (i :: M).filter (fun j => decide (¬ j ≤ k)) = i :: M := by
          rw [List.filter_cons, if_pos (by simpa using hi), hM2]
        rw [h1, h2, List.nil_append]

/-- **The coded sequence factors at any threshold.** -/
theorem elt_split (k : ℤ) (f : E) :
    elt f = elt (Finsupp.filter (fun i => i ≤ k) f)
      * elt (Finsupp.filter (fun i => ¬ i ≤ k) f) := by
  rw [elt_filter, elt_filter, ← eltOn_append,
    ← list_split_of_pairwise k (Finset.pairwise_sort _ _), ← elt_eq_eltOn_support]

/-! ## 7.  Membership in a coordinate subgroup -/

theorem eltOn_mem_closure {q : ℤ → Prop} {L : List ℤ} {f : E} (h : ∀ i ∈ L, q i) :
    eltOn L f ∈ Subgroup.closure (FreeGroup.of '' {i : ℤ | q i}) := by
  induction L with
  | nil =>
      rw [eltOn_nil]
      exact Subgroup.one_mem _
  | cons i M ih =>
      rw [eltOn_cons]
      refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _)
        (ih fun j hj => h j (List.mem_cons.mpr (Or.inr hj)))
      exact Subgroup.subset_closure ⟨i, h i (List.mem_cons.mpr (Or.inl rfl)), rfl⟩

theorem elt_mem_closure {q : ℤ → Prop} {f : E} (h : ∀ i ∈ f.support, q i) :
    elt f ∈ Subgroup.closure (FreeGroup.of '' {i : ℤ | q i}) := by
  rw [elt_eq_eltOn_support]
  refine eltOn_mem_closure fun i hi => h i ?_
  rwa [Finset.mem_sort] at hi

/-! ## 8.  Agreement on a set of coordinates -/

/-- Agreement on `p` is equality of the filtered sequences. -/
theorem filter_eq_iff_agree {p : ℤ → Prop} [DecidablePred p] {f g : E} :
    Finsupp.filter p f = Finsupp.filter p g ↔ ∀ i, p i → f i = g i := by
  constructor
  · intro h i hi
    have := congrArg (fun u : E => u i) h
    rwa [Finsupp.filter_apply, Finsupp.filter_apply, if_pos hi, if_pos hi] at this
  · intro h
    refine Finsupp.ext fun i => ?_
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hi : p i
    · rw [if_pos hi, if_pos hi]
      exact h i hi
    · rw [if_neg hi, if_neg hi]

/-- **Agreement on `p` makes the ratio of the codes die under the deletion.**
This is the forward inclusion of the operation identities: no splitting of the
sorted list is needed, only that the deletion is a homomorphism. -/
theorem killOn_ratio_eq_one {p : ℤ → Prop} [DecidablePred p] {f g : E}
    (h : ∀ i, p i → f i = g i) : killOn p ((elt g)⁻¹ * elt f) = 1 := by
  have hfg : Finsupp.filter p f = Finsupp.filter p g := filter_eq_iff_agree.mpr h
  rw [map_mul, map_inv, killOn_elt, killOn_elt, hfg, inv_mul_cancel]

/-- **Two sequences whose codes differ by something the deletion kills agree on
`p`.**  This is the reverse inclusion of the operation identities. -/
theorem agree_of_mul_ker {p : ℤ → Prop} [DecidablePred p] {f g : E}
    {w : FreeGroup ℤ} (hw : killOn p w = 1) (h : elt f = elt g * w) :
    ∀ i, p i → f i = g i := by
  refine filter_eq_iff_agree.mp ?_
  have hk := congrArg (killOn p) h
  rw [killOn_elt, map_mul, killOn_elt, hw, mul_one] at hk
  exact elt_injective hk

/-- The special case in which the difference is supported off `p`. -/
theorem filter_eq_of_mul_mem {p : ℤ → Prop} [DecidablePred p] {f g : E}
    {w : FreeGroup ℤ} (hw : w ∈ Subgroup.closure (FreeGroup.of '' {i : ℤ | ¬ p i}))
    (h : elt f = elt g * w) :
    Finsupp.filter p f = Finsupp.filter p g :=
  filter_eq_iff_agree.mpr (agree_of_mul_ker (killOn_eq_one_of_mem_closure hw) h)

end Split
end Higman
end GroupApproximation
