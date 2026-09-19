import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# A segment of a geodesic word is a geodesic word

The first of the two facts Lemma 5.9 needs.  Its proof of the gap statement runs
the penetration half of Lemma 4.8 on the sub-path between two consecutive
separating cosets, and that requires the sub-path to be a geodesic word in its
own right, between the vertices it joins.

Both directions of the length clause are already in the tree and neither is
hard; what makes the segment a geodesic is that the two bounds meet:

* at most `j - i`, because the segment itself spells the difference of the two
  vertices, in `j - i` letters (`wordNorm_listVal_le`);
* at least `j - i`, because the whole word is geodesic
  (`sub_le_wordDist_vertex`).

The segment is `(w.drop i).take (j - i)`, the form `listVal_take_split` is
stated in.

Unconditional: no leaf, no bound, no hypothesis beyond `i ≤ j ≤ |w|`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A segment spells the difference of its endpoints.** -/
theorem listVal_segment (w : List (RelLetter G Λ)) (f : G) {i j : ℕ}
    (hij : i ≤ j) :
    vertex f w i * RelLetter.listVal ((w.drop i).take (j - i)) = vertex f w j := by
  rw [vertex_eq_mul_listVal_take w f i, vertex_eq_mul_listVal_take w f j,
    mul_assoc, listVal_take_split w i j hij]

/-- **A segment of a geodesic word is a geodesic word.** -/
theorem isGeodesicWord_segment (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ w.length) :
    IsGeodesicWord D (vertex f w i) (vertex f w j)
      ((w.drop i).take (j - i)) := by
  have hlet : ∀ a ∈ (w.drop i).take (j - i), D.IsLetter a := fun a ha =>
    hw.1 a (List.drop_subset i w (List.take_subset (j - i) _ ha))
  have hlen : ((w.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨hlet, listVal_segment w f hij, ?_⟩
  have hval : (vertex f w i)⁻¹ * vertex f w j
      = RelLetter.listVal ((w.drop i).take (j - i)) := by
    rw [← listVal_segment w f hij]
    group
  have hle : wordDist D.alphabet.carrier (vertex f w i) (vertex f w j) ≤ j - i := by
    show wordNorm D.alphabet.carrier
      ((vertex f w i)⁻¹ * vertex f w j) ≤ j - i
    rw [hval]
    have hstep := wordNorm_listVal_le D ((w.drop i).take (j - i)) hlet
    omega
  have hge := sub_le_wordDist_vertex D hw i j hij hj
  omega

omit [Group G] in
/-- **Reading a letter of a segment.**  Both `List.getElem_take` and
`List.getElem_drop` are simp lemmas at this revision, so the composite is one
step; it is named because the index shift `a ↦ i + a` is what the component
transfer of Lemma 5.9 is stated in. -/
theorem getElem_segment (w : List (RelLetter G Λ)) (i m a : ℕ)
    (ha : a < ((w.drop i).take m).length) (hw : i + a < w.length) :
    ((w.drop i).take m)[a]'ha = w[i + a]'hw := by
  simp

end OsinComponents
end GGT
end GroupApproximation
