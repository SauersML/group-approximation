import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral

/-!
# Normalising an avoiding path: no two components connected

This is a NORMALISATION step, not progress towards `IsolatedComponentBound`.
It cannot approach the bound's `C * n`: the base stretches between components
that are *not* connected survive it untouched, and those run along quasi-geodesic
sides of unbounded length.  What it delivers is a path in which every remaining
component is isolated *in that path*, which is the hypothesis shape the
geometric estimate consumes.

## The splice

If two component starts `i < j` of an avoiding path are `Connected`, the element
`z = (vertex 1 u i)⁻¹ * vertex 1 u j` they span lies in `H lam`, so the whole
stretch between them can be replaced by the single letter `comp lam z`:

    u' = u.take i ++ comp lam z :: u.drop j .

The result is admissible, spells the same element, and is strictly shorter,
because `two_le_of_isCompStart` (OsinTheorem54SepFourGonGeneral) puts two
distinct component starts at least two apart.

It is still avoiding, and this is the point: the new letter is read at the vertex
`vertex 1 u i`, which the original path already visited carrying a `lam`-letter,
so `avoidsFrom_iff_forall` puts it outside `H lam`.  Avoidance is therefore
preserved by construction at every step rather than re-established at the end.
The remaining letters keep their vertices — the prefix is untouched, and the
suffix resumes at `vertex 1 u i * z = vertex 1 u j`.

## What is cited

`avoidsFrom_append`, `avoidsFrom_take`, `avoidsFrom_drop` and
`vertex_eq_mul_listVal_take` are osin-ah4's, in `OsinTheorem54SeparatingCosets`
and `OsinTheorem54SepSplit`; `two_le_of_isCompStart` is theirs in
`OsinTheorem54SepFourGonGeneral`; `avoidsFrom_iff_forall` is in
`DGOIsolatedComponentBridge`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  A component letter is read outside the subgroup -/

/-- **On an avoiding path, a `lam`-letter is read outside `H lam`.**  This is
`avoidsFrom_iff_forall` read in the direction the splice needs. -/
theorem notMem_fam_vertex_of_avoidsFrom (H : Λ → Subgroup G) (lam : Λ)
    {u : List (RelLetter G Λ)} (hav : AvoidsFrom H lam u 1) {i : ℕ}
    (hi : i < u.length) (hci : (u[i]'hi).IsCompOf lam) :
    vertex (1 : G) u i ∉ H lam :=
  (avoidsFrom_iff_forall H lam u 1).mp hav i hi hci

/-! ## 2.  The splice -/

/-- **Two connected components can be spliced together.**  The stretch between
them is replaced by the single letter they span; the result is admissible,
spells the same element, is still avoiding, and is strictly shorter. -/
theorem exists_splice (D : RelGenSet G Λ) (lam : Λ)
    {u : List (RelLetter G Λ)} (hlet : ∀ a ∈ u, D.IsLetter a)
    (hav : AvoidsFrom D.fam lam u 1) {i j : ℕ}
    (hij : i + 1 < j) (hju : j ≤ u.length) (hi : i < u.length)
    (hci : (u[i]'hi).IsCompOf lam)
    (hconn : Connected D.fam lam 1 u i j) :
    ∃ u' : List (RelLetter G Λ), (∀ a ∈ u', D.IsLetter a) ∧
      RelLetter.listVal u' = RelLetter.listVal u ∧
      AvoidsFrom D.fam lam u' 1 ∧ u'.length < u.length := by
  classical
  have hvi : vertex (1 : G) u i = RelLetter.listVal (u.take i) := by
    rw [vertex_eq_mul_listVal_take u 1 i, one_mul]
  have hvj : vertex (1 : G) u j = RelLetter.listVal (u.take j) := by
    rw [vertex_eq_mul_listVal_take u 1 j, one_mul]
  have hzmul : vertex (1 : G) u i
      * ((vertex (1 : G) u i)⁻¹ * vertex (1 : G) u j) = vertex (1 : G) u j := by
    group
  refine ⟨u.take i ++ RelLetter.comp lam
      ((vertex (1 : G) u i)⁻¹ * vertex (1 : G) u j) :: u.drop j, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hlet a (List.take_subset i u h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact hconn
      · exact hlet a (List.drop_subset j u h)
  · have hcons : RelLetter.listVal (RelLetter.comp lam
        ((vertex (1 : G) u i)⁻¹ * vertex (1 : G) u j) :: u.drop j)
        = ((vertex (1 : G) u i)⁻¹ * vertex (1 : G) u j)
          * RelLetter.listVal (u.drop j) := by
      simp [RelLetter.listVal, RelLetter.val]
    have hsplit : RelLetter.listVal (u.take j) * RelLetter.listVal (u.drop j)
        = RelLetter.listVal u := by
      rw [← listVal_append, List.take_append_drop]
    rw [listVal_append, hcons, ← mul_assoc, ← hvi, hzmul, hvj, hsplit]
  · refine (avoidsFrom_append D.fam lam _ _ 1).mpr
      ⟨avoidsFrom_take D.fam lam 1 u i hav, ?_⟩
    rw [one_mul, ← hvi]
    refine ⟨?_, ?_⟩
    · rintro ⟨-, hmem⟩
      exact notMem_fam_vertex_of_avoidsFrom D.fam lam hav hi hci hmem
    · show AvoidsFrom D.fam lam (u.drop j)
        (vertex (1 : G) u i * ((vertex (1 : G) u i)⁻¹ * vertex (1 : G) u j))
      rw [hzmul]
      exact avoidsFrom_drop D.fam lam 1 u j hav
  · simp only [List.length_append, List.length_cons, List.length_take,
      List.length_drop]
    omega

/-! ## 3.  The normalisation -/

/-- **Every avoiding path reduces to one in which no two components are
connected.**  Repeated splicing; the length strictly drops each time. -/
theorem exists_reduced (D : RelGenSet G Λ) (lam : Λ) :
    ∀ (n : ℕ) (u : List (RelLetter G Λ)), u.length ≤ n →
      (∀ a ∈ u, D.IsLetter a) → AvoidsFrom D.fam lam u 1 →
      ∃ u' : List (RelLetter G Λ), (∀ a ∈ u', D.IsLetter a) ∧
        RelLetter.listVal u' = RelLetter.listVal u ∧
        AvoidsFrom D.fam lam u' 1 ∧ u'.length ≤ u.length ∧
        ∀ i j : ℕ, i ≠ j → IsCompStart lam u' i → IsCompStart lam u' j →
          ¬ Connected D.fam lam 1 u' i j := by
  classical
  intro n
  induction n with
  | zero =>
      intro u hun hlet hav
      refine ⟨u, hlet, rfl, hav, le_rfl, ?_⟩
      intro i j _ hi _ _
      obtain ⟨k, hk1, hk2, -, -, -⟩ := hi
      have hz : u.length = 0 := Nat.le_zero.mp hun
      omega
  | succ n ih =>
      intro u hun hlet hav
      by_cases hpair : ∃ i j : ℕ, i < j ∧ IsCompStart lam u i ∧
          IsCompStart lam u j ∧ Connected D.fam lam 1 u i j
      · obtain ⟨i, j, hij, hi, hj, hconn⟩ := hpair
        have h2 : i + 2 ≤ j := two_le_of_isCompStart hi hj hij
        obtain ⟨ki, hki1, hki2, hki3, -, -⟩ := hi
        obtain ⟨kj, hkj1, hkj2, -, -, -⟩ := hj
        have hiu : i < u.length := by omega
        have hju : j ≤ u.length := by omega
        have hci : (u[i]'hiu).IsCompOf lam := hki3 i le_rfl hki1 hiu
        obtain ⟨u', hlet', hval', hav', hlen'⟩ :=
          exists_splice D lam hlet hav (by omega) hju hiu hci hconn
        obtain ⟨u'', hlet'', hval'', hav'', hlen'', hred''⟩ :=
          ih u' (by omega) hlet' hav'
        exact ⟨u'', hlet'', by rw [hval'', hval'], hav'', by omega, hred''⟩
      · refine ⟨u, hlet, rfl, hav, le_rfl, ?_⟩
        intro i j hne hi hj hconn
        rcases Nat.lt_or_ge i j with hlt | hge
        · exact hpair ⟨i, j, hlt, hi, hj, hconn⟩
        · exact hpair ⟨j, i, by omega, hj, hi, connected_symm hconn⟩

end OsinComponents
end GGT
end GroupApproximation
