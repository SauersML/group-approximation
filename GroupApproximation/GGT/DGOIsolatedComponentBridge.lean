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

end OsinComponents
end GGT
end GroupApproximation
