import GroupApproximation.GGT.DGOTwoConnectorSplice
import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex

/-!
# The six-block splice, for two connectors that cross

`DGOTwoConnectorSplice.cycle_of_two_connectors` handles the two-connector case
of Dahmani--Guirardel--Osin's Lemma 4.16 when the two index pairs do not
interleave: splicing the far pair first leaves the near pair intact, so the
second splice is `cycle_of_connector` again.  When they *do* interleave --- when
the near-vertex produced by the offset on the side *preceding* the component
comes before the one produced by the offset on the side *following* it --- there
is no order in which the two splices compose, because each deletes an index the
other needs.

The cycle Dahmani--Guirardel--Osin write for that configuration traverses a
segment of the polygon **backwards**, and that is what this module builds:

    q = w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))

with `m ≤ j ≤ m' ≤ j'`, the connector `r` running from `vertex v w m` **forward
past** `vertex v w j` to `vertex v w m'`, and the connector `r'` running from
`vertex v w j` --- which the reversed block has walked back to --- on to
`vertex v w j'`.  The crossing `m ≤ j ≤ m' ≤ j'` with `r` joining the *outer*
pair and `r'` the *inner* pair is exactly the interleaving that
`cycle_of_two_connectors` excludes, and the reversal is what makes it a path.

## Why the reversed block needs no offset

A connector is allowed into the cycle only because *no vertex of it* lies in the
coset `v · H lam` --- in `cycle_of_connector` that is the hypothesis `hrcos`,
supplied by the corner offset of `notMem_coset_vertex_of_offset`.  The reversed
block gets the same conclusion from a different source, and a stronger one: its
letters are the inverses of letters of `w`, so `isCompOf_invLetter` makes a
`lam`-letter of the block a `lam`-letter of `w`, and its vertices are vertices of
`w`; isolatedness of the distinguished component then forbids the coset directly,
through `notMem_coset_of_isIsolated_zero`.  No offset is available for it --- the
block runs along a side at bounded distance from the basepoint --- and none is
needed.

The transfer is made once, in the vocabulary of `AvoidsFrom`, rather than letter
by letter: `avoidsFrom_iff_forall` turns "no `lam`-letter of the segment is read
at a coset vertex" into `AvoidsFrom` for the segment read from `v⁻¹ · a₋`, and
`avoidsFrom_revWord` --- which is precisely the statement that avoidance is a
property of the *edge* and not of its orientation --- turns that into the same
statement for the reversed block read from the far end.  Reading it back through
`avoidsFrom_iff_forall` is the hypothesis the assembly wants.  This avoids
identifying `(revWord s)[t]` with a letter of `w` by index arithmetic, and with it
the off-by-one between the letter at a reversed index and the vertex it is read
at.

## What is proved

* `listVal_drop_of_closed` --- the tail of a closed word spells the way back to
  the basepoint.  This is what lets the last block return.
* `vertex_revSegment` --- the vertices of the reversed block are the vertices of
  `w` between `j` and `m'`, in decreasing order.  Not used by the assembly, which
  works at the block's own basepoint, but it is the geometric statement that
  makes the length bookkeeping `m' - j` honest, and it is `vertex_revWord`'s
  intended consumer.
* `vertex_revSplice` --- the vertices of `q` in the five ranges;
  `getElem_revSplice_left`, `_conn`, `_rev`, `_conn'` and `_right` --- its letters.
* `letters_revSplice`, `length_revSplice` --- admissibility and length.
* `cycle_of_reversed_splice` --- the theorem, with the same conclusion as
  `cycle_of_connector`: a closed admissible word carrying the same span as an
  isolated `H lam`-component at `0`, of length
  `m + |r| + (m' - j) + |r'| + (|w| - j')`.

## The one hypothesis this splice has and the others do not

`revWord` inverts every letter, so an `X`-letter reverses to an `X`-letter only
if `D.base` is closed under inversion.  That is the hypothesis `hsymm`, and it is
free: `OsinTheorem54SepSymmetric.exists_symmetric_base` supplies it, and
`relBall_of_isolated_of_closed` --- the only consumer of any of these cycles ---
already carries it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The tail of a closed word -/

/-- **The tail of a closed word spells the way back to the basepoint.**  Read
from `vertex v w t`, the word `w.drop t` ends at `v`.  In `cycle_of_connector`
this is proved inline; the six-block splice needs it in the same form, so it is
named here. -/
theorem listVal_drop_of_closed (v : G) {w : List (RelLetter G Λ)}
    (hcl : RelLetter.listVal w = 1) (t : ℕ) :
    RelLetter.listVal (w.drop t) = (vertex v w t)⁻¹ * v := by
  have hAB : RelLetter.listVal (w.take t) * RelLetter.listVal (w.drop t) = 1 := by
    rw [← listVal_append, List.take_append_drop]
    exact hcl
  have htj : RelLetter.listVal (w.take t) = v⁻¹ * vertex v w t := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  rw [htj] at hAB
  calc RelLetter.listVal (w.drop t)
      = (v⁻¹ * vertex v w t)⁻¹ *
          ((v⁻¹ * vertex v w t) * RelLetter.listVal (w.drop t)) := by group
    _ = (v⁻¹ * vertex v w t)⁻¹ := by rw [hAB, mul_one]
    _ = (vertex v w t)⁻¹ * v := by group

/-! ## The reversed block -/

/-- **The value of a segment, as a span.**  `listVal_segment` states it
multiplicatively; this is the same fact solved for the segment. -/
theorem listVal_segment_eq (v : G) (w : List (RelLetter G Λ)) {j k : ℕ}
    (hjk : j ≤ k) :
    RelLetter.listVal ((w.drop j).take (k - j))
      = (vertex v w j)⁻¹ * vertex v w k := by
  rw [← listVal_segment w v hjk, inv_mul_cancel_left]

/-- **The reversed segment walks back along `w`.**  Its vertex at parameter `t`
is `vertex v w (m' - t)`: reading `revWord ((w.drop j).take (m' - j))` from
`vertex v w m'` retraces the segment `[j, m']` of `w` in the opposite direction,
so the block has `m' - j` letters and ends at `vertex v w j`.

This is `vertex_revWord` --- the index reversal `t ↦ |s| - t` --- composed with
`vertex_segment`, which identifies the vertices of a segment with the vertices of
the word it was cut from. -/
theorem vertex_revSegment (v : G) (w : List (RelLetter G Λ)) {j m' : ℕ}
    (hjm : j ≤ m') (hm'w : m' ≤ w.length) {t : ℕ} (ht : t ≤ m' - j) :
    vertex (vertex v w m') (revWord ((w.drop j).take (m' - j))) t
      = vertex v w (m' - t) := by
  have hslen : ((w.drop j).take (m' - j)).length = m' - j :=
    length_segment w j (m' - j) (by omega)
  have hsval : RelLetter.listVal ((w.drop j).take (m' - j))
      = (vertex v w j)⁻¹ * vertex v w m' := listVal_segment_eq v w hjm
  have hpre : vertex (1 : G) ((w.drop j).take (m' - j)) (m' - j - t)
      = (vertex v w j)⁻¹ * vertex v w (m' - t) := by
    have h : vertex (vertex v w j) ((w.drop j).take (m' - j)) (m' - j - t)
        = vertex v w (j + (m' - j - t)) :=
      vertex_segment w v j (m' - j) (m' - j - t) (by omega)
    rw [show j + (m' - j - t) = m' - t from by omega,
      vertex_eq_mul_vertex_one ((w.drop j).take (m' - j)) (vertex v w j)
        (m' - j - t)] at h
    rw [← h]
    group
  have hrev := vertex_revWord ((w.drop j).take (m' - j)) (vertex v w m')
    (m' - j - t)
  rw [hslen, show m' - j - (m' - j - t) = t from by omega, hsval, hpre] at hrev
  rw [hrev]
  group

/-! ## Length and letters of the six-block word -/

/-- **The six-block word has `m + |r| + (m' - j) + |r'| + (|w| - j')`
letters.** -/
theorem length_revSplice (w r r' : List (RelLetter G Λ)) {m j m' j' : ℕ}
    (hmw : m ≤ w.length) (hjm : j ≤ m') (hm'w : m' ≤ w.length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j')))).length
      = m + r.length + (m' - j) + r'.length + (w.length - j') := by
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  simp only [List.length_append, List.length_take_of_le hmw, hlenB,
    List.length_drop]
  omega

/-- **Every letter of the six-block word is admissible.**  The reversed block is
where the base has to be closed under inversion. -/
theorem letters_revSplice (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {w r r' : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hr'let : ∀ a ∈ r', D.IsLetter a) (m j m' j' : ℕ) :
    ∀ a ∈ w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j'))), D.IsLetter a := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hlet a (List.take_subset m w h)
  rcases List.mem_append.mp h with h | h
  · exact hrlet a h
  rcases List.mem_append.mp h with h | h
  · exact isLetter_of_mem_revWord D hsymm
      (fun b hb => hlet b (List.drop_subset j w
        (List.take_subset (m' - j) (w.drop j) hb))) a h
  rcases List.mem_append.mp h with h | h
  · exact hr'let a h
  · exact hlet a (List.drop_subset j' w h)

/-! ## Vertices of the six-block word -/

/-- **The vertices of the six-block word**, in the five ranges: the prefix of
`w`, the first connector, the reversed block (given at the block's own basepoint
`vertex v w m'`, which is what the isolation argument reads), the second
connector, and the suffix of `w`. -/
theorem vertex_revSplice (v : G) (w r r' : List (RelLetter G Λ)) {m j m' j' : ℕ}
    (hmw : m ≤ w.length) (hjm : j ≤ m') (hm'w : m' ≤ w.length)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w m')
    (hr'val : RelLetter.listVal r' = (vertex v w j)⁻¹ * vertex v w j') :
    (∀ i : ℕ, i ≤ m →
        vertex v (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
          (r' ++ w.drop j')))) i = vertex v w i) ∧
      (∀ t : ℕ, t ≤ r.length →
        vertex v (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
          (r' ++ w.drop j')))) (m + t) = vertex (vertex v w m) r t) ∧
      (∀ t : ℕ, t ≤ m' - j →
        vertex v (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
          (r' ++ w.drop j')))) (m + r.length + t)
          = vertex (vertex v w m') (revWord ((w.drop j).take (m' - j))) t) ∧
      (∀ t : ℕ, t ≤ r'.length →
        vertex v (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
          (r' ++ w.drop j')))) (m + r.length + (m' - j) + t)
          = vertex (vertex v w j) r' t) ∧
      (∀ t : ℕ,
        vertex v (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
          (r' ++ w.drop j')))) (m + r.length + (m' - j) + r'.length + t)
          = vertex v w (j' + t)) := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  have hvA : v * RelLetter.listVal (w.take m) = vertex v w m :=
    (vertex_eq_mul_listVal_take w v m).symm
  have hvr : vertex v w m * RelLetter.listVal r = vertex v w m' := by
    rw [hrval]
    group
  have hvB : vertex v w m' *
      RelLetter.listVal (revWord ((w.drop j).take (m' - j))) = vertex v w j := by
    rw [listVal_revWord, listVal_segment_eq v w hjm]
    group
  have hvr' : vertex v w j * RelLetter.listVal r' = vertex v w j' := by
    rw [hr'val]
    group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [vertex_append_of_le (w.take m)
      (r ++ (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j'))) v i
      (by omega)]
    exact vertex_take_eq v w m i hi
  · intro t ht
    rw [show m + t = (w.take m).length + t from by omega, vertex_append_add, hvA]
    exact vertex_append_of_le r
      (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j'))
      (vertex v w m) t ht
  · intro t ht
    rw [show m + r.length + t = (w.take m).length + (r.length + t) from by omega,
      vertex_append_add, hvA, vertex_append_add, hvr]
    exact vertex_append_of_le (revWord ((w.drop j).take (m' - j)))
      (r' ++ w.drop j') (vertex v w m') t (by omega)
  · intro t ht
    rw [show m + r.length + (m' - j) + t
        = (w.take m).length + (r.length +
            ((revWord ((w.drop j).take (m' - j))).length + t)) from by omega,
      vertex_append_add, hvA, vertex_append_add, hvr, vertex_append_add, hvB]
    exact vertex_append_of_le r' (w.drop j') (vertex v w j) t ht
  · intro t
    rw [show m + r.length + (m' - j) + r'.length + t
        = (w.take m).length + (r.length +
            ((revWord ((w.drop j).take (m' - j))).length +
              (r'.length + t))) from by omega,
      vertex_append_add, hvA, vertex_append_add, hvr, vertex_append_add, hvB,
      vertex_append_add, hvr',
      vertex_eq_mul_vertex_one (w.drop j') (vertex v w j') t]
    exact vertex_drop_eq w v j' t

/-! ## Letters of the six-block word -/

/-- **A letter of the prefix.** -/
theorem getElem_revSplice_left (w r r' : List (RelLetter G Λ)) {m j m' j' i : ℕ}
    (hmw : m ≤ w.length) (hi : i < m)
    (h' : i < (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j'))))[i]'h' = w[i]'(by omega) := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  rw [List.getElem_append_left (by omega : i < (w.take m).length)]
  simp

/-- **A letter of the first connector.** -/
theorem getElem_revSplice_conn (w r r' : List (RelLetter G Λ)) {m j m' j' i : ℕ}
    (hmw : m ≤ w.length) (hi1 : m ≤ i) (hi2 : i < m + r.length)
    (hb : i - m < r.length)
    (h' : i < (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j'))))[i]'h' = r[i - m]'hb := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_left (by omega : i - (w.take m).length < r.length)]
  congr 1
  omega

/-- **A letter of the reversed block.** -/
theorem getElem_revSplice_rev (w r r' : List (RelLetter G Λ)) {m j m' j' i : ℕ}
    (hmw : m ≤ w.length) (hjm : j ≤ m') (hm'w : m' ≤ w.length)
    (hi1 : m + r.length ≤ i) (hi2 : i < m + r.length + (m' - j))
    (hb : i - m - r.length < (revWord ((w.drop j).take (m' - j))).length)
    (h' : i < (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j'))))[i]'h'
      = (revWord ((w.drop j).take (m' - j)))[i - m - r.length]'hb := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_right (by omega : r.length ≤ i - (w.take m).length),
    List.getElem_append_left (by omega :
      i - (w.take m).length - r.length
        < (revWord ((w.drop j).take (m' - j))).length)]
  congr 1
  omega

/-- **A letter of the second connector.** -/
theorem getElem_revSplice_conn' (w r r' : List (RelLetter G Λ)) {m j m' j' i : ℕ}
    (hmw : m ≤ w.length) (hjm : j ≤ m') (hm'w : m' ≤ w.length)
    (hi1 : m + r.length + (m' - j) ≤ i)
    (hi2 : i < m + r.length + (m' - j) + r'.length)
    (hb : i - m - r.length - (m' - j) < r'.length)
    (h' : i < (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j'))))[i]'h'
      = r'[i - m - r.length - (m' - j)]'hb := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_right (by omega : r.length ≤ i - (w.take m).length),
    List.getElem_append_right (by omega :
      (revWord ((w.drop j).take (m' - j))).length
        ≤ i - (w.take m).length - r.length),
    List.getElem_append_left (by omega :
      i - (w.take m).length - r.length
          - (revWord ((w.drop j).take (m' - j))).length < r'.length)]
  congr 1
  omega

/-- **A letter of the suffix.** -/
theorem getElem_revSplice_right (w r r' : List (RelLetter G Λ)) {m j m' j' i : ℕ}
    (hmw : m ≤ w.length) (hjm : j ≤ m') (hm'w : m' ≤ w.length)
    (hi1 : m + r.length + (m' - j) + r'.length ≤ i)
    (hb : j' + (i - m - r.length - (m' - j) - r'.length) < w.length)
    (h' : i < (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length) :
    (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
        (r' ++ w.drop j'))))[i]'h'
      = w[j' + (i - m - r.length - (m' - j) - r'.length)]'hb := by
  have hlenm : (w.take m).length = m := List.length_take_of_le hmw
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  rw [List.getElem_append_right (by omega : (w.take m).length ≤ i),
    List.getElem_append_right (by omega : r.length ≤ i - (w.take m).length),
    List.getElem_append_right (by omega :
      (revWord ((w.drop j).take (m' - j))).length
        ≤ i - (w.take m).length - r.length),
    List.getElem_append_right (by omega :
      r'.length ≤ i - (w.take m).length - r.length
        - (revWord ((w.drop j).take (m' - j))).length),
    List.getElem_drop]
  congr 1
  omega

/-! ## The splice -/

/-- **The six-block splice of two crossing connectors.**

Given the polygon `w` with an isolated `H lam`-component as its first letter,
four indices `m ≤ j ≤ m' ≤ j'`, a connector `r` from `vertex v w m` to
`vertex v w m'` and a connector `r'` from `vertex v w j` to `vertex v w j'` ---
so the two pairs *cross*, which is exactly what `cycle_of_two_connectors`
excludes --- with no vertex of either connector in the coset `v · H lam`, the
word

    q = w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))

is a closed admissible path carrying the same span as an isolated component at
`0`, of length `m + |r| + (m' - j) + |r'| + (|w| - j')`.

The conclusion is the conclusion of `cycle_of_connector`, so the branch of
Dahmani--Guirardel--Osin's Case 4 that needs this one ends exactly like the
others.

Where each hypothesis is spent, as in `cycle_of_connector`: closedness of `w`
returns the last block to the basepoint (`listVal_drop_of_closed`); the two
connector hypotheses `hrcos`, `hr'cos` rule out coset vertices along `r` and
`r'`; isolatedness rules them out along the prefix, the reversed block and the
suffix.  `2 ≤ m` is again free --- `hrcos` at `p = 0` says `vertex v w m` is
outside the coset, while `vertex v w 0` and `vertex v w 1` are both inside it. -/
theorem cycle_of_reversed_splice (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {m j m' j' : ℕ} (h1 : m ≤ j) (h2 : j ≤ m') (h3 : m' ≤ j')
    (h4 : j' ≤ w.length)
    {r r' : List (RelLetter G Λ)}
    (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w m')
    (hrcos : ∀ p : ℕ, p ≤ r.length →
      v⁻¹ * vertex (vertex v w m) r p ∉ D.fam lam)
    (hr'let : ∀ a ∈ r', D.IsLetter a)
    (hr'val : RelLetter.listVal r' = (vertex v w j)⁻¹ * vertex v w j')
    (hr'cos : ∀ p : ℕ, p ≤ r'.length →
      v⁻¹ * vertex (vertex v w j) r' p ∉ D.fam lam) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length = m + r.length + (m' - j) + r'.length + (w.length - j') ∧
      IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  have hmw : m ≤ w.length := by omega
  have hm'w : m' ≤ w.length := by omega
  -- the first connector starts outside the coset, so it starts past the component
  have hm0 : m ≠ 0 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    simp only [vertex_zero, inv_mul_cancel]
    exact one_mem _
  have hm1 : m ≠ 1 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    have hspan := span_mem_fam_of_isComp D v hlet hcomp
    rw [vertex_zero] at hspan
    simpa only [vertex_zero] using hspan
  have hm2 : 2 ≤ m := by omega
  have h1w : 1 ≤ w.length := hcomp.2.1
  obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ :=
    vertex_revSplice v w r r' hmw h2 hm'w hrval hr'val
  have hlenB : (revWord ((w.drop j).take (m' - j))).length = m' - j := by
    rw [length_revWord, length_segment w j (m' - j) (by omega)]
  have hqlen : (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
      (r' ++ w.drop j')))).length
      = m + r.length + (m' - j) + r'.length + (w.length - j') :=
    length_revSplice w r r' hmw h2 hm'w
  -- the reversed block, through the avoidance vocabulary
  have hslet : ∀ a ∈ (w.drop j).take (m' - j), D.IsLetter a := fun a ha =>
    hlet a (List.drop_subset j w (List.take_subset (m' - j) (w.drop j) ha))
  have hslen : ((w.drop j).take (m' - j)).length = m' - j :=
    length_segment w j (m' - j) (by omega)
  have hsval : RelLetter.listVal ((w.drop j).take (m' - j))
      = (vertex v w j)⁻¹ * vertex v w m' := listVal_segment_eq v w h2
  have hfwd : AvoidsFrom D.fam lam ((w.drop j).take (m' - j))
      (v⁻¹ * vertex v w j) := by
    refine (avoidsFrom_iff_forall D.fam lam _ _).mpr ?_
    intro x hx hcx
    have hxlt : x < m' - j := by omega
    have hpw : j + x < w.length := by omega
    have hcp : (w[j + x]'hpw).IsCompOf lam := by
      simpa only [List.getElem_take, List.getElem_drop] using hcx
    have hveq : vertex (v⁻¹ * vertex v w j) ((w.drop j).take (m' - j)) x
        = v⁻¹ * vertex v w (j + x) := by
      rw [vertex_smul, vertex_segment w v j (m' - j) x (by omega)]
    rw [hveq]
    exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso hpw hcp
      (by omega)
  have hbase : (v⁻¹ * vertex v w j) *
      RelLetter.listVal ((w.drop j).take (m' - j)) = v⁻¹ * vertex v w m' := by
    rw [hsval]
    group
  have hrevav : AvoidsFrom D.fam lam (revWord ((w.drop j).take (m' - j)))
      (v⁻¹ * vertex v w m') := by
    have h := (avoidsFrom_revWord D lam ((w.drop j).take (m' - j)) hslet
      (v⁻¹ * vertex v w j)).mpr hfwd
    rwa [hbase] at h
  have hrevcos : ∀ (t : ℕ)
      (ht : t < (revWord ((w.drop j).take (m' - j))).length),
      ((revWord ((w.drop j).take (m' - j)))[t]'ht).IsCompOf lam →
        v⁻¹ * vertex (vertex v w m') (revWord ((w.drop j).take (m' - j))) t
          ∉ D.fam lam := by
    intro t ht hc
    have h := (avoidsFrom_iff_forall D.fam lam _ _).mp hrevav t ht hc
    rwa [vertex_smul] at h
  -- the first letter is the component, the second is not
  have hw0 : (w[0]'(by omega)).IsCompOf lam :=
    hcomp.2.2.1 0 le_rfl (by omega) (by omega)
  have hw1 : ∀ hh : 1 < w.length, ¬ (w[1]'hh).IsCompOf lam := hcomp.2.2.2.2
  have hqcomp : IsComp lam (w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j))
      ++ (r' ++ w.drop j')))) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro i _ hi1 hiq
      have hi0 : i = 0 := by omega
      subst hi0
      rw [getElem_revSplice_left w r r' hmw (by omega) hiq]
      exact hw0
    · intro i hcon
      exact absurd hcon (by omega)
    · intro hk hcon
      rw [getElem_revSplice_left w r r' hmw (by omega) hk] at hcon
      exact hw1 (by omega) hcon
  have htm : RelLetter.listVal (w.take m) = v⁻¹ * vertex v w m := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  refine ⟨w.take m ++ (r ++ (revWord ((w.drop j).take (m' - j)) ++
    (r' ++ w.drop j'))), letters_revSplice D hsymm hlet hrlet hr'let m j m' j',
    ?_, hqlen, hqcomp, ?_, ?_⟩
  · rw [listVal_append, listVal_append, listVal_append, listVal_append, htm,
      hrval, listVal_revWord, hsval, hr'val, listVal_drop_of_closed v hcl j']
    group
  · refine isIsolated_zero_of_notMem D lam v hqcomp ?_
    intro i hine hiq hci
    have hilen : i < m + r.length + (m' - j) + r'.length + (w.length - j') := by
      rw [← hqlen]
      exact hiq
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [getElem_revSplice_left w r r' hmw hlt hiq] at hci
      rw [hv1 i (le_of_lt hlt)]
      exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso (p := i)
        (by omega) hci (Nat.pos_of_ne_zero hine)
    · rcases Nat.lt_or_ge i (m + r.length) with hlt2 | hge2
      · have hveq : vertex v (w.take m ++ (r ++
            (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))) i
            = vertex (vertex v w m) r (i - m) := by
          have h := hv2 (i - m) (by omega)
          rwa [show m + (i - m) = i from by omega] at h
        rw [hveq]
        exact hrcos (i - m) (by omega)
      · rcases Nat.lt_or_ge i (m + r.length + (m' - j)) with hlt3 | hge3
        · have hb : i - m - r.length
              < (revWord ((w.drop j).take (m' - j))).length := by omega
          have hveq : vertex v (w.take m ++ (r ++
              (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))) i
              = vertex (vertex v w m')
                  (revWord ((w.drop j).take (m' - j))) (i - m - r.length) := by
            have h := hv3 (i - m - r.length) (by omega)
            rwa [show m + r.length + (i - m - r.length) = i from by omega] at h
          rw [getElem_revSplice_rev w r r' hmw h2 hm'w hge2 hlt3 hb hiq] at hci
          rw [hveq]
          exact hrevcos (i - m - r.length) hb hci
        · rcases Nat.lt_or_ge i (m + r.length + (m' - j) + r'.length) with
            hlt4 | hge4
          · have hveq : vertex v (w.take m ++ (r ++
                (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))) i
                = vertex (vertex v w j) r'
                    (i - m - r.length - (m' - j)) := by
              have h := hv4 (i - m - r.length - (m' - j)) (by omega)
              rwa [show m + r.length + (m' - j) + (i - m - r.length - (m' - j))
                = i from by omega] at h
            rw [hveq]
            exact hr'cos (i - m - r.length - (m' - j)) (by omega)
          · have hb : j' + (i - m - r.length - (m' - j) - r'.length)
                < w.length := by omega
            have hveq : vertex v (w.take m ++ (r ++
                (revWord ((w.drop j).take (m' - j)) ++ (r' ++ w.drop j')))) i
                = vertex v w
                    (j' + (i - m - r.length - (m' - j) - r'.length)) := by
              have h := hv5 (i - m - r.length - (m' - j) - r'.length)
              rwa [show m + r.length + (m' - j) + r'.length
                + (i - m - r.length - (m' - j) - r'.length) = i
                from by omega] at h
            rw [getElem_revSplice_right w r r' hmw h2 hm'w hge4 hb hiq] at hci
            rw [hveq]
            exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso
              (p := j' + (i - m - r.length - (m' - j) - r'.length))
              (by omega) hci (by omega)
  · rw [hv1 0 (by omega), hv1 1 (by omega)]

end OsinComponents
end GGT
end GroupApproximation
