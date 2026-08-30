import GroupApproximation.GGT.HullEeSplice
import GroupApproximation.GGT.HullEeTransfer

/-!
# A shortest word's `E`-components are isolated

This closes the isolation half of Hull's Lemma `ee`, joining the three pieces
that were built separately.

`GGT/HullEeSplice.lean` says a shortest admissible avoiding word has no two
positions, two or more apart, whose vertices differ by an element of the base.
`GGT/HullEeTransfer.lean` says the transported word has the same vertices as the
original and that its components are exactly the `E`-letters.  What is left is to
observe that these are the same statement read in two vocabularies, and that
`OsinComponents.two_le_of_isCompStart` supplies the "two or more apart" from the
maximality of components.

So the estimate's isolation hypothesis is discharged, and it is discharged by
minimality rather than assumed.

## The three facts that have to line up

* **The separation.**  `Connected` compares two component STARTS, and
  `two_le_of_isCompStart` turns `i < j` into `i + 2 ≤ j` because a component is a
  maximal run.  That is exactly the hypothesis the splice needs, and it is why
  the splice was stated with `i + 2 ≤ j` rather than `i < j`.
* **The vertices.**  `Connected` in `D_E` is about the vertices of the
  transported word; the splice is about the vertices of the original.
  `vertex_map_transferLetter` says these are equal --- the translation renames
  letters and never changes the element one names, so the path is the same path.
* **The membership.**  `Connected` puts the difference in `D_E`'s family, which
  is `E`; the splice needs it in the enlarged base, which is `X ∪ E`.  The
  enlargement is what bridges them, and it is the reason the whole argument is
  about `relGenSetAddSubgroup` rather than about `D`.

## Symmetry, which costs one step and is easy to forget

`IsIsolated` quantifies over every other component start, on both sides, while
`two_le_of_isCompStart` wants a strict inequality in a fixed direction.
`Connected` is symmetric --- the two differences are inverses and a subgroup is
closed under inversion --- so the case `j < i` is the case `i < j` read
backwards.  That step is `OsinComponents.connected_symm`, which already exists in
this namespace; an earlier draft of this module reproved it, and `dupcheck`
caught the collision before a probe was spent.  It would have been a
same-namespace redeclaration, which is the shape that breaks the root rather than
one module.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Isolated

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A shortest word admits no connection between two `E`-components.**

The heart of the isolation step.  `Connected` in `D_E` says the two vertices
differ by an element of `E`; the enlargement has put `E` into the base; and the
splice says a shortest word has no such pair once the two positions are two or
more apart, which `two_le_of_isCompStart` supplies from maximality. -/
theorem not_connected_transfer_of_minimal {D : RelGenSet G Λ} {E : Subgroup G}
    {DE : RelGenSet G Unit} (hfam : DE.fam = fun _ => E) {lam : Λ} {h : G}
    {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, (relGenSetAddSubgroup D E).IsLetter a)
    (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom (relGenSetAddSubgroup D E).fam lam w 1)
    (hmin : ∀ v : List (RelLetter G Λ),
      (∀ a ∈ v, (relGenSetAddSubgroup D E).IsLetter a) →
        RelLetter.listVal v = h →
          AvoidsFrom (relGenSetAddSubgroup D E).fam lam v 1 →
            w.length ≤ v.length)
    {i j : ℕ} (hij : i < j)
    (hi : IsCompStart () (w.map (transferLetter E)) i)
    (hj : IsCompStart () (w.map (transferLetter E)) j) :
    ¬ Connected DE.fam () 1 (w.map (transferLetter E)) i j := by
  intro hconn
  have hsep : i + 2 ≤ j := two_le_of_isCompStart hi hj hij
  have hjlen : j ≤ w.length := by
    obtain ⟨k, hk⟩ := hj
    have h1 : j < k := hk.1
    have h2 : k ≤ (w.map (transferLetter E)).length := hk.2.1
    rw [length_map_transferLetter] at h2
    omega
  have hE : (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j ∈ E := by
    have hc : (vertex (1 : G) (w.map (transferLetter E)) i)⁻¹
        * vertex (1 : G) (w.map (transferLetter E)) j ∈ DE.fam () := hconn
    rw [hfam] at hc
    rwa [vertex_map_transferLetter, vertex_map_transferLetter] at hc
  have hbase : (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j
      ∈ (relGenSetAddSubgroup D E).base := by
    show (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j ∈ D.base ∪ (E : Set G)
    exact Set.mem_union_right _ (SetLike.mem_coe.mpr hE)
  exact not_mem_base_of_minimal hlet hval hav hmin hsep hjlen hbase

/-- **Every `E`-component of a shortest word is isolated.**

This is the form the isolated-component estimate consumes.  Both orders of the
two indices reduce to the previous theorem, the second through `connected_symm`.

Nothing here is geometric: no hyperbolicity, no constant, no polygon.  Isolation
in Hull's argument is bought entirely by minimality, and this is where that is
cashed. -/
theorem isIsolated_transfer_of_minimal {D : RelGenSet G Λ} {E : Subgroup G}
    {DE : RelGenSet G Unit} (hfam : DE.fam = fun _ => E) {lam : Λ} {h : G}
    {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, (relGenSetAddSubgroup D E).IsLetter a)
    (hval : RelLetter.listVal w = h)
    (hav : AvoidsFrom (relGenSetAddSubgroup D E).fam lam w 1)
    (hmin : ∀ v : List (RelLetter G Λ),
      (∀ a ∈ v, (relGenSetAddSubgroup D E).IsLetter a) →
        RelLetter.listVal v = h →
          AvoidsFrom (relGenSetAddSubgroup D E).fam lam v 1 →
            w.length ≤ v.length)
    {i : ℕ} (hi : IsCompStart () (w.map (transferLetter E)) i) :
    IsIsolated DE.fam () 1 (w.map (transferLetter E)) i := by
  refine ⟨hi, ?_⟩
  intro j hji hj hconn
  rcases lt_or_gt_of_ne (Ne.symm hji) with hlt | hgt
  · exact not_connected_transfer_of_minimal hfam hlet hval hav hmin hlt hi hj
      hconn
  · exact not_connected_transfer_of_minimal hfam hlet hval hav hmin hgt hj hi
      (connected_symm hconn)

end Isolated

end OsinComponents
end GGT
end GroupApproximation
