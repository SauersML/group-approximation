import GroupApproximation.Sofic.SmallCancellationRouter

/-!
# A decision toolkit for `C'(1/6)` on an explicit finite relator family

`MetricSmallCancellation R lam` quantifies over every piece and every member of
`symmetrization R`, which is a set of rotations and formal inverses.  Checking
it by exhausting subwords of the avatar family is not viable in the kernel: the
words are long by design.  This module replaces the exhaustion by three
separable obligations, each about the *code* the words are built from.

## The reduction

`metricSmallCancellation_of_bounds` is the workhorse.  It needs only

* an upper bound `pmax` on the length of any piece, and
* a lower bound `lmin` on the length of any symmetrized relator,

and the rational inequality `pmax < lam * lmin`.  The two bounds are proved
independently, and neither mentions the other.

The relator bound is free: rotation and formal inversion preserve length, so
`symmetrization_length_ge` reduces it to a check on the finite family itself.

The piece bound is the real content, and `pieceLength_le_of_tag` is where the
code structure enters.  A *tag* is a partial reading of a word's opening
feature — for the avatar code, the pair of exponents of its first two complete
`y₂`-runs.  Three properties of the tag suffice:

* `hstable`: a tag read off a prefix is the tag of the whole word;
* `hlong`: any word longer than `pmax` carries a tag (it contains two complete
  runs);
* `hpin`: two members of the family carrying the same tag are equal.

A piece longer than `pmax` would then carry a tag, that tag would be shared by
the two distinct family members it prefixes, and `hpin` would identify them.
So no piece is longer than `pmax`, with no subword enumeration anywhere.

`hpin` is the design obligation the avatar code discharges: exponent ranges are
pairwise disjoint and each exponent occurs once, so a consecutive exponent pair
names the avatar and the position inside it, hence the rotation offset, hence
the word.
-/

namespace GroupApproximation
namespace SmallCancellationDecision

open SmallCancellationRouter

variable {α : Type*} {β : Type*}

/-! ## Length control transfers across symmetrization -/

/-- Every symmetrized relator has the length of some relator: rotation and
formal inversion are length-preserving. -/
theorem exists_length_eq_of_mem_symmetrization {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    ∃ r ∈ R, w.length = r.length := by
  obtain ⟨r, hr, n, h | h⟩ := hw
  · exact ⟨r, hr, by rw [h, List.length_rotate]⟩
  · exact ⟨r, hr, by rw [h, List.length_rotate, FreeGroup.invRev_length]⟩

/-- A uniform lower bound on relator length lifts to the symmetrization. -/
theorem symmetrization_length_ge {R : Set (List (α × Bool))} {lmin : ℕ}
    (h : ∀ r ∈ R, lmin ≤ r.length) :
    ∀ w ∈ symmetrization R, lmin ≤ w.length := by
  intro w hw
  obtain ⟨r, hr, hlen⟩ := exists_length_eq_of_mem_symmetrization hw
  rw [hlen]
  exact h r hr

/-! ## The ratio reduction -/

/-- **The workhorse.**  A piece-length upper bound and a relator-length lower
bound whose ratio beats `lam` give the metric condition outright. -/
theorem metricSmallCancellation_of_bounds {R : Set (List (α × Bool))}
    {lam : ℚ} {pmax lmin : ℕ} (hlam : 0 ≤ lam)
    (hpiece : ∀ p, IsPiece (symmetrization R) p → p.length ≤ pmax)
    (hlen : ∀ w ∈ symmetrization R, lmin ≤ w.length)
    (hratio : (pmax : ℚ) < lam * (lmin : ℚ)) :
    MetricSmallCancellation R lam := by
  intro p hp w hw _
  have h1 : (p.length : ℚ) ≤ (pmax : ℚ) := by exact_mod_cast hpiece p hp
  have h2 : (lmin : ℚ) ≤ (w.length : ℚ) := by exact_mod_cast hlen w hw
  have h3 : lam * (lmin : ℚ) ≤ lam * (w.length : ℚ) :=
    mul_le_mul_of_nonneg_left h2 hlam
  linarith

/-! ## The piece bound from a positional code -/

/-- **The code bound.**  A prefix-stable partial tag that is defined on long
words and separates the family bounds every piece by `pmax`.

No subword enumeration occurs: the only inputs are the three displayed
properties of the tag. -/
theorem pieceLength_le_of_tag {S : Set (List (α × Bool))}
    {tag : List (α × Bool) → Option β} {pmax : ℕ}
    (hstable : ∀ p w : List (α × Bool), p <+: w →
      ∀ t, tag p = some t → tag w = some t)
    (hpin : ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ t,
      tag w₁ = some t → tag w₂ = some t → w₁ = w₂)
    (hlong : ∀ p : List (α × Bool), pmax < p.length → (tag p).isSome)
    {p : List (α × Bool)} (hp : IsPiece S p) :
    p.length ≤ pmax := by
  by_contra hcon
  have hcon' : pmax < p.length := lt_of_not_ge hcon
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, hp₁, hp₂⟩ := hp
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hlong p hcon')
  exact hne (hpin w₁ hw₁ w₂ hw₂ t (hstable p w₁ hp₁ t ht)
    (hstable p w₂ hp₂ t ht))

/-- **The packaged entry point.**  Everything the avatar family must supply in
order to be `C'(lam)`, with the family-specific content confined to `hpin`. -/
theorem metricSmallCancellation_of_tag {R : Set (List (α × Bool))}
    {tag : List (α × Bool) → Option β} {lam : ℚ} {pmax lmin : ℕ}
    (hlam : 0 ≤ lam)
    (hstable : ∀ p w : List (α × Bool), p <+: w →
      ∀ t, tag p = some t → tag w = some t)
    (hpin : ∀ w₁ ∈ symmetrization R, ∀ w₂ ∈ symmetrization R, ∀ t,
      tag w₁ = some t → tag w₂ = some t → w₁ = w₂)
    (hlong : ∀ p : List (α × Bool), pmax < p.length → (tag p).isSome)
    (hrel : ∀ r ∈ R, lmin ≤ r.length)
    (hratio : (pmax : ℚ) < lam * (lmin : ℚ)) :
    MetricSmallCancellation R lam :=
  metricSmallCancellation_of_bounds hlam
    (fun _ hp => pieceLength_le_of_tag hstable hpin hlong hp)
    (symmetrization_length_ge hrel) hratio

/-! ## Cyclic reducedness of positive words

The avatars are positive words, and a positive word can cancel nowhere — at a
junction or across the wrap. -/

/-- A word with no inverse letters is reduced. -/
theorem isReduced_of_forall_pos {L : List (α × Bool)}
    (h : ∀ x ∈ L, x.2 = true) : FreeGroup.IsReduced L := by
  induction L with
  | nil => simp [FreeGroup.IsReduced]
  | cons x xs ih =>
      cases xs with
      | nil => simp [FreeGroup.IsReduced]
      | cons y ys =>
          refine List.IsChain.cons
            (ih fun z hz => h z (List.mem_cons_of_mem _ hz)) ?_
          intro b hb _
          rw [h x List.mem_cons_self,
            h b (List.mem_cons_of_mem _ (List.mem_of_mem_head? hb))]

/-- A word with no inverse letters is cyclically reduced. -/
theorem isCyclicallyReduced_of_forall_pos {L : List (α × Bool)}
    (h : ∀ x ∈ L, x.2 = true) : FreeGroup.IsCyclicallyReduced L := by
  refine ⟨isReduced_of_forall_pos h, ?_⟩
  intro a ha b hb _
  rw [h a (List.mem_of_mem_getLast? ha), h b (List.mem_of_mem_head? hb)]

end SmallCancellationDecision
end GroupApproximation
