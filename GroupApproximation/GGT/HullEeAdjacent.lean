import GroupApproximation.GGT.HullEeCycleComponents

/-!
# A shortest word has no two adjacent `E`-letters, so its `E`-components are single letters

The isolated-component estimate bounds the **span** of a component --- the
product of its letters --- not the letters themselves.  For Hull's Lemma `ee`
that is not enough on its own: what has to land in a finite set is each
`E`-letter, so that the whole word can be rewritten over a finitely enlarged
base.  The two coincide exactly when every `E`-component is a single letter, and
that is what this module proves.

It is another consequence of minimality, and it is the same collapse as before
read at the shortest possible gap.  If two adjacent letters both name elements of
`E`, their product names an element of `E`, so the two of them can be replaced by
the one letter naming that product --- a shorter admissible word for the same
element, still avoiding `Γ_{H_λ}`.  That is precisely
`HullEeSplice.not_mem_base_of_minimal` at `j = i + 2`, the tightest instance the
splice admits, and the reason the splice was proved at general `j` rather than
only where the earlier argument needed it.

## Why this is not the same fact as isolation

Isolation ruled out two *components* connected to one another, which are two or
more apart by maximality.  This rules out two *letters* adjacent to one another,
which is the case maximality does not reach --- adjacent `E`-letters do not form
two components, they form one component of length two.  So the two facts are
disjoint instances of one collapse, and both are needed: isolation to apply the
estimate at all, and this to read its conclusion letter by letter.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Adjacent

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  Reading a component letter back through the translation -/

/-- **Only an `E`-letter becomes a component.**  The converse of the three
`isCompOf` lemmas of `GGT/HullEeTransfer.lean`, assembled: a transported letter
is a component exactly when the original was a base letter naming an element of
`E`. -/
theorem exists_base_of_isCompOf_transferLetter {E : Subgroup G}
    {a : RelLetter G Λ} (h : (transferLetter E a).IsCompOf ()) :
    ∃ x : G, a = RelLetter.base x ∧ x ∈ E := by
  cases a with
  | base x =>
      by_cases hx : x ∈ E
      · exact ⟨x, rfl, hx⟩
      · exact absurd h (not_isCompOf_transferLetter_base_of_notMem hx)
  | comp mu y => exact absurd h (not_isCompOf_transferLetter_comp E mu y)

/-- Indexing commutes with the translation.

No `omit` here, unlike the list-only lemmas of `GGT/HullEeCycleComponents.lean`:
`transferLetter` is stated over `Subgroup G`, so it carries `[Group G]` and every
statement mentioning it uses the instance. -/
theorem getElem_map_transferLetter {E : Subgroup G} (v : List (RelLetter G Λ))
    {m : ℕ} (hm : m < v.length) (hm' : m < (v.map (transferLetter E)).length) :
    (v.map (transferLetter E))[m]'hm' = transferLetter E (v[m]'hm) :=
  List.getElem_map _

/-! ## 2.  Adjacent `E`-letters are forbidden -/

/-- **A shortest word has no two adjacent letters naming elements of `E`.**

The collapse at the tightest gap the splice admits.  Their product lies in `E`,
hence in the enlarged base, and `j = i + 2` is exactly the hypothesis
`not_mem_base_of_minimal` wants. -/
theorem not_adjacent_mem_of_minimal {D : RelGenSet G Λ} {E : Subgroup G}
    {lam : Λ} {h : G} {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, (relGenSetAddSubgroup D E).IsLetter a)
    (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom (relGenSetAddSubgroup D E).fam lam w 1)
    (hmin : ∀ v : List (RelLetter G Λ),
      (∀ a ∈ v, (relGenSetAddSubgroup D E).IsLetter a) →
        RelLetter.listVal v = h →
          AvoidsFrom (relGenSetAddSubgroup D E).fam lam v 1 →
            w.length ≤ v.length)
    {i : ℕ} (hi0 : i < w.length) (hi1 : i + 1 < w.length)
    (h0 : (w[i]'hi0).val ∈ E) (h1 : (w[i + 1]'hi1).val ∈ E) : False := by
  have hstep1 : vertex (1 : G) w (i + 1) = vertex (1 : G) w i * (w[i]'hi0).val :=
    vertex_succ w 1 i hi0
  have hstep2 : vertex (1 : G) w (i + 2)
      = vertex (1 : G) w (i + 1) * (w[i + 1]'hi1).val :=
    vertex_succ w 1 (i + 1) hi1
  have hprod : (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w (i + 2)
      = (w[i]'hi0).val * (w[i + 1]'hi1).val := by
    rw [hstep2, hstep1]
    group
  have hmem : (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w (i + 2)
      ∈ (relGenSetAddSubgroup D E).base := by
    rw [hprod]
    show (w[i]'hi0).val * (w[i + 1]'hi1).val ∈ D.base ∪ (E : Set G)
    exact Set.mem_union_right _ (SetLike.mem_coe.mpr (mul_mem h0 h1))
  exact not_mem_base_of_minimal hlet hval hav hmin (i := i) (j := i + 2)
    (le_refl _) (by omega) hmem

/-! ## 3.  Every `E`-component is a single letter -/

/-- **A component of the transported shortest word has length one.**

So the estimate's bound on the span of a component is a bound on the letter
itself, which is what lets the whole word be rewritten over a base enlarged by a
finite set. -/
theorem isComp_transfer_eq_succ {D : RelGenSet G Λ} {E : Subgroup G} {lam : Λ}
    {h : G} {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, (relGenSetAddSubgroup D E).IsLetter a)
    (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom (relGenSetAddSubgroup D E).fam lam w 1)
    (hmin : ∀ v : List (RelLetter G Λ),
      (∀ a ∈ v, (relGenSetAddSubgroup D E).IsLetter a) →
        RelLetter.listVal v = h →
          AvoidsFrom (relGenSetAddSubgroup D E).fam lam v 1 →
            w.length ≤ v.length)
    {i k : ℕ} (hc : IsComp () (w.map (transferLetter E)) i k) : k = i + 1 := by
  obtain ⟨hik, hkl, hall, -, -⟩ := hc
  have hlenmap : (w.map (transferLetter E)).length = w.length :=
    length_map_transferLetter E w
  by_contra hne
  have hi0 : i < w.length := by omega
  have hi1 : i + 1 < w.length := by omega
  have hpA : i < (w.map (transferLetter E)).length := by omega
  have hpB : i + 1 < (w.map (transferLetter E)).length := by omega
  have hA := hall i (le_refl i) (by omega) hpA
  have hB := hall (i + 1) (by omega) (by omega) hpB
  rw [getElem_map_transferLetter w hi0 hpA] at hA
  rw [getElem_map_transferLetter w hi1 hpB] at hB
  obtain ⟨x, hxeq, hxE⟩ := exists_base_of_isCompOf_transferLetter hA
  obtain ⟨y, hyeq, hyE⟩ := exists_base_of_isCompOf_transferLetter hB
  refine not_adjacent_mem_of_minimal hlet hval hav hmin hi0 hi1 ?_ ?_
  · rw [hxeq]
    exact hxE
  · rw [hyeq]
    exact hyE

end Adjacent

end OsinComponents
end GGT
end GroupApproximation
