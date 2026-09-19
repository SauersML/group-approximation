import GroupApproximation.GGT.DGOReversedSplice

/-!
# Safe blocks: one splice for every cut of Dahmani--Guirardel--Osin's §4.2

`cycle_of_connector` splices a geodesic connector into a polygon.  Read its
hypotheses again and notice what they do *not* say: `hrlet` asks the spliced
block to be admissible, `hrval` asks it to spell `(vertex v w m)⁻¹ · vertex v w j`,
and `hrcos` asks that no `lam`-letter of it be read at a vertex of the coset.
Nothing requires the block to be a geodesic, or short, or a single piece.

That is the whole content of this module.  A block is **safe** exactly when it is
admissible and avoids `Γ_{H lam}` read from `(vertex v w i)⁻¹ · x` --- and
`AvoidsFrom` is already the repository's word for that, with its algebra already
proved:

* concatenation is `avoidsFrom_append`;
* reversal is `avoidsFrom_revWord`, which is precisely the statement that
  avoidance is a property of the *edge* and not of its orientation;
* the pointwise reading is `avoidsFrom_iff_forall`.

So the two mechanisms that Dahmani--Guirardel--Osin's §4.2 is usually presented
with --- a nested corner offset, and the split of their Lemma 4.17 --- are the
same construction seen from two sides, and both are instances of ONE splice whose
middle block happens to be a concatenation.  `cycle_of_connector`,
`cycle_of_two_connectors` and `cycle_of_reversed_splice` all become corollaries;
no further splice *shape* is ever needed, whatever the side count.

## What is proved

* `isIsolated_of_notMem` --- isolation at a general index `i`, with the
  components taken out.  The obligation is needed only away from the run
  `[i,k)`: a component start strictly inside the run would contradict its own
  previous-letter clause, and that is the only thing the index-`0` version
  (`isIsolated_zero_of_notMem`) got for free from `k = 1`.
* `cycle_of_avoiding_block` --- the splice, at a general index and with an
  arbitrary safe block.  No rotation and no collapse: the component
  `[i,k)` stays where it is, inside the retained prefix `w.take m`, and
  `relBall_of_isolated_of_closed` is already stated at general `(i,k)`.
* `avoidsFrom_of_offset` --- a connector is safe by the corner-offset count
  alone.
* `avoidsFrom_segment_of_isIsolated`, `avoidsFrom_revSegment_of_isIsolated` ---
  a segment of the polygon, traversed either way, is safe by isolation.

Those three families and `avoidsFrom_append` are a complete calculus: every cut
of every branch of the §4.2 case analysis is one application of
`cycle_of_avoiding_block` to a block built from them.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Isolation at a general index -/

/-- **Isolation of the component at `i`, with the components taken out.**

What has to be checked is only that no `lam`-letter *away from the run* is read
at a vertex of the coset.  Inside the run there is nothing to check, and that is
not an omission: a component start `j` with `i < j < k` would have `q[j-1]` a
`lam`-letter by the run clause of `[i,k)` and not a `lam`-letter by its own
previous-letter clause.

This is `isIsolated_zero_of_notMem` with the index freed.  At `i = 0`, `k = 1`
the range condition `j < i ∨ k ≤ j` collapses to `j ≠ 0`, which is what that
lemma asks. -/
theorem isIsolated_of_notMem (D : RelGenSet G Λ) (lam : Λ) (u : G)
    {q : List (RelLetter G Λ)} {i k : ℕ} (hcomp : IsComp lam q i k)
    (h : ∀ j : ℕ, (j < i ∨ k ≤ j) → ∀ hj : j < q.length,
      (q[j]'hj).IsCompOf lam →
        (vertex u q i)⁻¹ * vertex u q j ∉ D.fam lam) :
    IsIsolated D.fam lam u q i := by
  refine ⟨⟨k, hcomp⟩, ?_⟩
  rintro j hne ⟨k', hc'⟩ hconn
  have hjk : j < k' := hc'.1
  have hkq : k' ≤ q.length := hc'.2.1
  have hjq : j < q.length := by omega
  have hcj : (q[j]'hjq).IsCompOf lam := hc'.2.2.1 j le_rfl hjk hjq
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact h j (Or.inl hlt) hjq hcj hconn
  · rcases Nat.lt_or_ge j k with hjk2 | hge2
    · exfalso
      have hij : i < j := by omega
      have hj1 : j - 1 < q.length := by omega
      have hrun : (q[j - 1]'hj1).IsCompOf lam :=
        hcomp.2.2.1 (j - 1) (by omega) (by omega) hj1
      exact hc'.2.2.2.1 (j - 1) (by omega) hj1 hrun
    · exact h j (Or.inr hge2) hjq hcj hconn

/-! ## The splice -/

/-- **The splice, at a general index and with an arbitrary safe block.**

Given the polygon `w` with an isolated `H lam`-component at `[i,k)`, two indices
`k < m ≤ j ≤ |w|`, and a block `r` from `vertex v w m` to `vertex v w j` that is
admissible and **avoids `Γ_{H lam}` read from `(vertex v w i)⁻¹ · vertex v w m`**,
the word

    q = w.take m ++ (r ++ w.drop j)

is a closed admissible path in which `[i,k)` is still an isolated component with
literally the same span, of length `m + |r| + (|w| - j)`.

`k < m` is the only new index condition and it is not a restriction: the cut
starts at an offset point, which is at least `θ + 2` from the coset centre while
the far end of the component is one alphabet letter from it.  It is what makes
`q[k]` still be `w[k]`, so that the run's maximality survives the splice; were
the block allowed to start at `k` its first letter could itself be a
`lam`-letter and the component would grow.

Where each hypothesis is spent, as in `cycle_of_connector`: closedness of `w`
returns the suffix to the basepoint, `hrav` rules out coset vertices along the
block, and isolatedness rules them out along the retained prefix and suffix
through `notMem_coset_of_isIsolated`, which is already general in `i`, `k` and
the position. -/
theorem cycle_of_avoiding_block (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    (hiso : IsIsolated D.fam lam v w i) {m j : ℕ} (hkm : k < m) (hmj : m ≤ j)
    (hjw : j ≤ w.length) {r : List (RelLetter G Λ)}
    (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j)
    (hrav : AvoidsFrom D.fam lam r ((vertex v w i)⁻¹ * vertex v w m)) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length = m + r.length + (w.length - j) ∧
      IsComp lam q i k ∧ IsIsolated D.fam lam v q i ∧
      (vertex v q i)⁻¹ * vertex v q k = (vertex v w i)⁻¹ * vertex v w k := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hmw : m ≤ w.length := le_trans hmj hjw
  obtain ⟨hv1, hv2, hv3⟩ := vertex_splice v w r hmw hrval
  have hqlen : (w.take m ++ (r ++ w.drop j)).length
      = m + r.length + (w.length - j) := by
    rw [List.length_append, List.length_append, List.length_take,
      List.length_drop]
    omega
  -- the run and its two boundary letters all survive in the retained prefix
  have hqcomp : IsComp lam (w.take m ++ (r ++ w.drop j)) i k := by
    refine ⟨hik, by omega, ?_, ?_, ?_⟩
    · intro p hp1 hp2 hpq
      rw [getElem_splice_left (i := p) w r hmw (by omega) hpq]
      exact hcomp.2.2.1 p hp1 hp2 (by omega)
    · intro p hp hpq hcon
      rw [getElem_splice_left (i := p) w r hmw (by omega) hpq] at hcon
      exact hcomp.2.2.2.1 p hp (by omega) hcon
    · intro hk hcon
      rw [getElem_splice_left (i := k) w r hmw (by omega) hk] at hcon
      exact hcomp.2.2.2.2 (by omega) hcon
  -- the suffix returns to the basepoint
  have htm : RelLetter.listVal (w.take m) = v⁻¹ * vertex v w m := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have hvi : vertex v (w.take m ++ (r ++ w.drop j)) i = vertex v w i :=
    hv1 i (by omega)
  refine ⟨w.take m ++ (r ++ w.drop j), ?_, ?_, hqlen, hqcomp, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hlet a (List.take_subset m w h)
    · rcases List.mem_append.mp h with h' | h'
      · exact hrlet a h'
      · exact hlet a (List.drop_subset j w h')
  · rw [listVal_append, listVal_append, htm, hrval,
      listVal_drop_of_closed v hcl j]
    group
  · refine isIsolated_of_notMem D lam v hqcomp ?_
    intro p hout hpq hcp
    have hilen : p < m + r.length + (w.length - j) := by
      rw [← hqlen]
      exact hpq
    rw [hvi]
    rcases Nat.lt_or_ge p m with hlt | hge
    · rw [getElem_splice_left (i := p) w r hmw hlt hpq] at hcp
      rw [hv1 p (le_of_lt hlt)]
      intro hmem
      exact notMem_coset_of_isIsolated D lam v hlet hcomp hiso (p := p)
        (by omega) hcp hout hmem
    · rcases Nat.lt_or_ge p (m + r.length) with hlt2 | hge2
      · have hb : p - m < r.length := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) p
            = vertex (vertex v w m) r (p - m) := by
          have hh := hv2 (p - m) (by omega)
          rwa [show m + (p - m) = p from by omega] at hh
        rw [getElem_splice_mid (i := p) w r hge hlt2 hmw hpq] at hcp
        rw [hveq]
        have hh := (avoidsFrom_iff_forall D.fam lam r
          ((vertex v w i)⁻¹ * vertex v w m)).mp hrav (p - m) hb hcp
        rwa [vertex_smul] at hh
      · have hb : j + (p - m - r.length) < w.length := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) p
            = vertex v w (j + (p - m - r.length)) := by
          have hh := hv3 (p - m - r.length)
          rwa [show m + r.length + (p - m - r.length) = p from by omega] at hh
        rw [getElem_splice_right (i := p) w r hge2 hmw hpq] at hcp
        rw [hveq]
        intro hmem
        exact notMem_coset_of_isIsolated D lam v hlet hcomp hiso
          (p := j + (p - m - r.length)) hb hcp (Or.inr (by omega)) hmem
  · rw [hvi, hv1 k (by omega)]

/-! ## Safe blocks: the connector -/

/-- **A connector is safe by the corner-offset count.**  A block of length at
most `θ` read from a point at least `θ + 2` from the coset centre never reaches
the coset at all --- not merely never reads a `lam`-letter there --- so its
avoidance is free of any hypothesis about its letters.

This is `notMem_coset_vertex_of_offset` in the `AvoidsFrom` vocabulary, which is
the vocabulary `cycle_of_avoiding_block` consumes. -/
theorem avoidsFrom_of_offset (D : RelGenSet G Λ) (lam : Λ) {a x : G} {θ : ℕ}
    {r : List (RelLetter G Λ)} (hrlet : ∀ c ∈ r, D.IsLetter c)
    (hlen : r.length ≤ θ)
    (hoff : θ + 2 ≤ wordDist D.alphabet.carrier a x) :
    AvoidsFrom D.fam lam r (a⁻¹ * x) := by
  refine (avoidsFrom_iff_forall D.fam lam r (a⁻¹ * x)).mpr ?_
  intro p hp _
  rw [vertex_smul]
  exact notMem_coset_vertex_of_offset D hrlet hlen hoff (le_of_lt hp)

/-! ## Safe blocks: segments of the polygon -/

/-- **A segment of the polygon lying beyond the run is safe.**  Its letters are
letters of `w` and its vertices are vertices of `w`, so isolatedness forbids the
coset directly, through `notMem_coset_of_isIsolated`.  No offset is available for
such a block --- it may run right past the coset centre --- and none is needed. -/
theorem avoidsFrom_segment_of_isIsolated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) {s t : ℕ}
    (hst : s ≤ t) (htw : t ≤ w.length) (hout : k ≤ s) :
    AvoidsFrom D.fam lam ((w.drop s).take (t - s))
      ((vertex v w i)⁻¹ * vertex v w s) := by
  have hslen : ((w.drop s).take (t - s)).length = t - s :=
    length_segment w s (t - s) (by omega)
  refine (avoidsFrom_iff_forall D.fam lam _ _).mpr ?_
  intro x hx hcx
  have hxlt : x < t - s := by omega
  have hpw : s + x < w.length := by omega
  have hcp : (w[s + x]'hpw).IsCompOf lam := by
    simpa only [List.getElem_take, List.getElem_drop] using hcx
  have hveq : vertex ((vertex v w i)⁻¹ * vertex v w s)
      ((w.drop s).take (t - s)) x = (vertex v w i)⁻¹ * vertex v w (s + x) := by
    rw [vertex_smul, vertex_segment w v s (t - s) x (by omega)]
  rw [hveq]
  intro hmem
  exact notMem_coset_of_isIsolated D lam v hlet hcomp hiso hpw hcp
    (Or.inr (by omega)) hmem

/-- **The same segment traversed backwards is safe.**

`avoidsFrom_revWord` is the statement that avoidance is a property of the edge
and not of its orientation, so the reversed block inherits safety from the
forward one with no index arithmetic --- in particular with no off-by-one between
"the letter at reversed index `t`" and "the vertex it is read at", which is what
made the reversed splice's isolation clause delicate the first time. -/
theorem avoidsFrom_revSegment_of_isIsolated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) {s t : ℕ}
    (hst : s ≤ t) (htw : t ≤ w.length) (hout : k ≤ s) :
    AvoidsFrom D.fam lam (revWord ((w.drop s).take (t - s)))
      ((vertex v w i)⁻¹ * vertex v w t) := by
  have hfwd := avoidsFrom_segment_of_isIsolated D lam v hlet hcomp hiso hst htw
    hout
  have hslet : ∀ c ∈ (w.drop s).take (t - s), D.IsLetter c := fun c hc =>
    hlet c (List.drop_subset s w (List.take_subset (t - s) (w.drop s) hc))
  have hbase : ((vertex v w i)⁻¹ * vertex v w s) *
      RelLetter.listVal ((w.drop s).take (t - s))
      = (vertex v w i)⁻¹ * vertex v w t := by
    rw [listVal_segment_eq v w hst]
    group
  have hh := (avoidsFrom_revWord D lam ((w.drop s).take (t - s)) hslet
    ((vertex v w i)⁻¹ * vertex v w s)).mpr hfwd
  rwa [hbase] at hh

end OsinComponents
end GGT
end GroupApproximation
