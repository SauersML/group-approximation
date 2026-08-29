import GroupApproximation.GGT.DGOIsolatedComponentCoset
import GroupApproximation.GGT.OsinTheorem54SepRuns
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral

/-!
# Reading avoidance off positions, and what isolatedness forbids

The bridge to `IsolatedComponentBound` shows that the complement of an isolated
component is a path avoiding `Γ_{H lam}`, so the span of the component lies in a
relative ball.  Two things are needed that the repository does not have, and
both are here.

## Establishing avoidance, rather than transporting it

`OsinTheorem54SeparatingCosets.avoidsFrom_append`,
`OsinTheorem54SepSplit.avoidsFrom_take` and `avoidsFrom_drop`,
`OsinTheorem54SeparatingCosets.avoidsFrom_smul_left` and
`OsinTheorem54SepReversal.avoidsFrom_revWord` all carry avoidance from one word
to another.  None of them establishes it, and the bridge cannot start from a
word already known to avoid: it starts from the polygon `w`, which does not
avoid --- the isolated component is exactly what violates it.

`avoidsFrom_iff_forall` supplies the missing direction: avoidance is the
pointwise statement that no `lam`-letter is read at a vertex of `H lam`.  With
it the complement can be shown avoiding position by position.

## What isolatedness forbids

`notMem_coset_of_isIsolated` is the mathematical content.  A `lam`-letter of `w`
at a position outside the component `[i,k)` cannot be read at a vertex of the
coset `(vertex v w i) · H lam`.  The proof cites `SepRuns`: that position lies in
a component (`exists_isComp_of_isCompOf`), whose start is `Connected` to it by
`SepComponents.span_mem_fam`; were the vertex in the coset, that start would be
`Connected` to `i` as well, and `IsIsolated` forbids a second component of the
same coset.  `isComp_end_unique` is what rules out the remaining case, that the
second component is the first one under another name: a component is determined
by where it starts.

## Lemma 4.6, and where its two hypotheses are spent

`relBall_of_isolated_of_closed` is the conversion device of
Dahmani--Guirardel--Osin's §4.2: an isolated `H lam`-component of a *closed*
admissible word of length `n` has `d̂_lam(a₋, a₊) ≤ n`.  Every later step of that
section manufactures a short cycle carrying the component and then calls this
one; nothing else in §4.2 produces a `d̂_lam` bound.  It needs no hyperbolicity,
no relative presentation and no polygon theory, which is why it is proved here
rather than waiting on them.

The path is the complement `c.drop k ++ c.take i`.  Closedness is what joins the
tail to the head --- the tail ends at `v · listVal c = v`, where the head starts
--- and isolatedness, through `notMem_coset_of_isIsolated`, is what makes the
join avoid `Γ_{H lam}`.  Isolatedness is spent on *edges*: the complement may
enter the coset as often as it likes, and is forbidden only to read a
`lam`-letter there.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  Avoidance, position by position -/

/-- **A path avoids `Γ_{H lam}` exactly when no `lam`-letter of it is read at a
vertex of `H lam`.**  The definition is a fold along the word; this is the same
condition indexed by position, which is the form needed to *establish* avoidance
rather than transport it. -/
theorem avoidsFrom_iff_forall (H : Λ → Subgroup G) (lam : Λ) :
    ∀ (u : List (RelLetter G Λ)) (p : G),
      AvoidsFrom H lam u p ↔
        ∀ (j : ℕ) (hj : j < u.length), (u[j]'hj).IsCompOf lam →
          vertex p u j ∉ H lam := by
  intro u
  induction u with
  | nil =>
      intro p
      constructor
      · intro _ j hj _
        simp only [List.length_nil] at hj
        omega
      · intro _
        trivial
  | cons a t ih =>
      intro p
      constructor
      · rintro ⟨h0, htail⟩ j hj hc
        cases j with
        | zero =>
            intro hmem
            exact h0 ⟨hc, hmem⟩
        | succ m =>
            have hm : m < t.length := by
              simp only [List.length_cons] at hj
              omega
            exact (ih (p * a.val)).mp htail m hm hc
      · intro hall
        refine ⟨?_, (ih (p * a.val)).mpr ?_⟩
        · rintro ⟨hc, hmem⟩
          exact hall 0 (by simp) hc hmem
        · intro m hm hc
          refine hall (m + 1) ?_ hc
          simp only [List.length_cons]
          omega

/-! ## 2.  A component is determined by where it starts -/

omit [Group G] in
/-- **The end of a component is determined by its start.**  If the ends
differed, the letter at the smaller end would be a `lam`-letter by the longer
component's run clause and not one by the shorter component's end clause. -/
theorem isComp_end_unique {lam : Λ} {w : List (RelLetter G Λ)} {i k k' : ℕ}
    (h : IsComp lam w i k) (h' : IsComp lam w i k') : k = k' := by
  obtain ⟨hik, hkw, hrun, -, hend⟩ := h
  obtain ⟨hik', hkw', hrun', -, hend'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_ge k k' with hlt | hge
  · have hkw2 : k < w.length := by omega
    exact hend hkw2 (hrun' k (by omega) hlt hkw2)
  · have hlt' : k' < k := by omega
    have hkw2 : k' < w.length := by omega
    exact hend' hkw2 (hrun k' (by omega) hlt' hkw2)

/-! ## 3.  What isolatedness forbids -/

/-- **An isolated component's coset is met by no other `lam`-letter.**  This is
the step the complement path runs on: outside `[i,k)`, no `lam`-letter of `w` is
read at a vertex of `(vertex v w i) · H lam`. -/
theorem notMem_coset_of_isIsolated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i)
    {p : ℕ} (hp : p < w.length) (hcp : (w[p]'hp).IsCompOf lam)
    (hout : p < i ∨ k ≤ p) :
    ¬ Connected D.fam lam v w i p := by
  intro hconn
  obtain ⟨i', k', hi'p, hpk', hcomp'⟩ := exists_isComp_of_isCompOf lam w p hp hcp
  have hconn' : Connected D.fam lam v w i' p :=
    span_mem_fam D lam v hlet p (le_of_lt hp) i' hi'p
      (fun m hm1 hm2 hm => hcomp'.2.2.1 m hm1 (by omega) hm)
  have hne : i' ≠ i := by
    intro hii
    subst hii
    have hkk : k' = k := isComp_end_unique hcomp' hcomp
    omega
  exact hiso.2 i' hne ⟨k', hcomp'⟩
    (connected_trans hconn (connected_symm hconn'))

/-! ## 4.  Geodesic sides carry single-letter components -/

/-- **On a geodesic side a component is one letter.**  The span of a component
lies in `H lam`, hence is a single letter of the alphabet, so the two endpoints
are at distance at most one; a geodesic side realises `k - i` as that distance,
so `k - i ≤ 1`, and `i < k` closes it.

This is the `μ = 1`, `b = 0` case of the quasi-geodesic clause, stated in `ℕ`.
It is not the target — hull-relator2's relator-separation quadrilateral has
genuinely quasi-geodesic sides, so `IsolatedComponentBound` must be proved at
general `(μ, b)` — but at `b = 0` it collapses the run apparatus to "position `i`
carries a `lam`-letter and its neighbours do not", which is what Lemma 4.8 at
`n = 2` and Lemma 4.9 at `n = 3` consume.

The distance bound is osin-ah4's `wordDist_le_one_of_mem_fam`
(`OsinTheorem54SepFourGonGeneral`), which takes exactly the span that
`span_mem_fam_of_isComp` produces. -/
theorem isComp_eq_succ_of_geodesic (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k)
    (hgeo : k - i ≤ wordDist D.alphabet.carrier (vertex v w i) (vertex v w k)) :
    k = i + 1 := by
  have hspan : (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hcomp
  have hone : wordDist D.alphabet.carrier (vertex v w i) (vertex v w k) ≤ 1 :=
    wordDist_le_one_of_mem_fam D hspan
  have hik : i < k := hcomp.1
  omega


/-! ## 5.  The complement of an isolated component: Lemma 4.6 -/

/-- **A vertex past `k` is a vertex of the tail.**  Reading `w` for `k + j`
letters is reading it for `k` and then reading `w.drop k` for `j`.  The prefix
identity behind it is `List.take_add`.  No bound on `k` or `j` is needed: past
the end of the word both sides stall. -/
theorem vertex_drop_eq (w : List (RelLetter G Λ)) (v : G) (k j : ℕ) :
    vertex v w k * vertex (1 : G) (w.drop k) j = vertex v w (k + j) := by
  rw [vertex_eq_mul_listVal_take w v k,
    vertex_eq_mul_listVal_take (w.drop k) 1 j,
    vertex_eq_mul_listVal_take w v (k + j), List.take_add, listVal_append,
    one_mul, mul_assoc]

/-- **Dahmani--Guirardel--Osin, Lemma 4.6.**  *An isolated `H lam`-component of
a cycle of length `C` in `Γ(G, X ⊔ ℋ)` has `d̂_lam(a₋, a₊) ≤ C`.*

This is the only device in their §4.2 that turns geometry into a bound on
`d̂_lam`.  Everything later in that section --- the corner-offset construction of
their Lemma 4.16, the split move of their Lemma 4.17, the Ol'shanskii cut behind
Proposition 4.14 --- exists to manufacture a *short* cycle in which the given
component is still isolated, and then calls this.  It is itself unconditional:
no hyperbolicity, no relative presentation, no polygon theory.

The path is the complement of the component, read from `a₊` round to `a₋`, which
is the word `c.drop k ++ c.take i`.  Two hypotheses do the work.

*Closedness* is what lets the tail be followed by the head: `c.drop k` ends at
`v · listVal c = v`, which is where `c.take i` starts.  In the proof this is
`hB`, that the tail spells the inverse of the head.

*Isolatedness* is what makes the complement avoid `Γ_{H lam}`: a `lam`-letter of
`c` at a position outside `[i, k)` read at a vertex of the coset
`(vertex v c i) · H lam` would start a second component of that coset, and
`notMem_coset_of_isIsolated` forbids it.  Note where the hypothesis is spent ---
on *edges*, not on vertices.  The complement may pass through the coset as often
as it likes; what it may not do is read a `lam`-letter there.

The conclusion is stated for the span, while the complement spells its inverse,
so `relBall_inv` turns the path round at the end.  That is the only use of the
symmetry hypothesis on `D.base`, and
`OsinTheorem54SepSymmetric.exists_symmetric_base` supplies it. -/
theorem relBall_of_isolated_of_closed (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) (v : G)
    {c : List (RelLetter G Λ)} (hlet : ∀ a ∈ c, D.IsLetter a)
    (hcl : RelLetter.listVal c = 1) {i k : ℕ}
    (hcomp : IsComp lam c i k) (hiso : IsIsolated D.fam lam v c i) :
    (vertex v c i)⁻¹ * vertex v c k ∈ D.relBall lam c.length := by
  have hik : i < k := hcomp.1
  have hkc : k ≤ c.length := hcomp.2.1
  have hic : i ≤ c.length := by omega
  have hspan : (vertex v c i)⁻¹ * vertex v c k ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hcomp
  -- the cycle closes: the tail spells the inverse of the head
  have hAB : RelLetter.listVal (c.take k) * RelLetter.listVal (c.drop k) = 1 := by
    rw [← listVal_append, List.take_append_drop]
    exact hcl
  have hB : RelLetter.listVal (c.drop k) = (RelLetter.listVal (c.take k))⁻¹ := by
    have hA : RelLetter.listVal (c.take k) = (RelLetter.listVal (c.drop k))⁻¹ :=
      eq_inv_of_mul_eq_one_left hAB
    rw [hA, inv_inv]
  -- what isolatedness forbids, read from the far end of the component
  have hkey : ∀ p : ℕ, ∀ hp : p < c.length, (c[p]'hp).IsCompOf lam →
      (p < i ∨ k ≤ p) → (vertex v c k)⁻¹ * vertex v c p ∉ D.fam lam := by
    intro p hp hcp hout hmem
    have hik' : Connected D.fam lam v c i k := hspan
    have hkp : Connected D.fam lam v c k p := hmem
    exact notMem_coset_of_isIsolated D lam v hlet hcomp hiso hp hcp hout
      (connected_trans hik' hkp)
  -- the tail avoids `Γ_{H lam}`
  have hdrop : AvoidsFrom D.fam lam (c.drop k) 1 := by
    refine (avoidsFrom_iff_forall D.fam lam (c.drop k) 1).mpr ?_
    intro j hj hcj
    have hjlen : j < c.length - k := by
      simpa only [List.length_drop] using hj
    have hp : k + j < c.length := by omega
    have hcp : (c[k + j]'hp).IsCompOf lam := by
      simpa only [List.getElem_drop] using hcj
    have hv : vertex (1 : G) (c.drop k) j
        = (vertex v c k)⁻¹ * vertex v c (k + j) := by
      rw [← vertex_drop_eq c v k j, inv_mul_cancel_left]
    rw [hv]
    exact hkey (k + j) hp hcp (Or.inr (Nat.le_add_right k j))
  -- the head avoids it too, read from the vertex the tail ends at
  have htake : AvoidsFrom D.fam lam (c.take i)
      (1 * RelLetter.listVal (c.drop k)) := by
    refine (avoidsFrom_iff_forall D.fam lam (c.take i)
      (1 * RelLetter.listVal (c.drop k))).mpr ?_
    intro m hm hcm
    have hmlt : m < i ∧ m < c.length := by
      simpa only [List.length_take, Nat.lt_min] using hm
    obtain ⟨hmi, hp⟩ := hmlt
    have hcp : (c[m]'hp).IsCompOf lam := by
      simpa only [List.getElem_take] using hcm
    have hv : vertex (1 * RelLetter.listVal (c.drop k)) (c.take i) m
        = (vertex v c k)⁻¹ * vertex v c m := by
      rw [vertex_take_eq (1 * RelLetter.listVal (c.drop k)) c i m (le_of_lt hmi),
        hB, vertex_eq_mul_listVal_take c (1 * (RelLetter.listVal (c.take k))⁻¹) m,
        vertex_eq_mul_listVal_take c v k, vertex_eq_mul_listVal_take c v m]
      group
    rw [hv]
    exact hkey m hp hcp (Or.inl hmi)
  -- assemble the complement, then turn it round
  have hinv : ((vertex v c i)⁻¹ * vertex v c k)⁻¹ ∈ D.relBall lam c.length := by
    refine ⟨inv_mem hspan, c.drop k ++ c.take i, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hlet a (List.drop_subset k c h)
      · exact hlet a (List.take_subset i c h)
    · rw [listVal_append, hB, vertex_eq_mul_listVal_take c v i,
        vertex_eq_mul_listVal_take c v k]
      group
    · exact (avoidsFrom_append D.fam lam (c.drop k) (c.take i) 1).mpr
        ⟨hdrop, htake⟩
    · rw [List.length_append, List.length_drop, List.length_take,
        Nat.min_eq_left hic]
      omega
  have hfinal := relBall_inv D lam hsymm hinv
  rwa [inv_inv] at hfinal

end OsinComponents
end GGT
end GroupApproximation
