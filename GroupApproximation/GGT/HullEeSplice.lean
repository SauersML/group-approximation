import GroupApproximation.GGT.HullEeMinimalWord
import GroupApproximation.GGT.OsinTheorem54SepSurgery
import GroupApproximation.GGT.DGOIsolatedComponentBridge

/-!
# Collapsing a segment, and why a shortest word has no connected pair

This is the step of Hull's Lemma `ee` that turns minimality into isolation.

The isolated-component estimate applies to a component that is **isolated**, and
isolation fails exactly when two components are *connected* --- when the vertices
at which they start differ by an element of the family.  What this module shows
is that a shortest word cannot have such a pair: if `vertex i` and `vertex j`
differ by `g`, the whole segment between them can be replaced by the single
letter naming `g`, and the result is a shorter word spelling the same element,
admissibly, still avoiding `Γ_{H_λ}`.

So isolation is not an extra hypothesis to be arranged.  **It is what minimality
already bought**, and this module is the receipt.

## Why the collapse is strictly shorter

Two *distinct* component starts are never adjacent.  A component is a maximal
run, so between the end of the run beginning at `i` and the start of the run
beginning at `j` there is at least one letter that is not a component letter of
that index; hence `j ≥ i + 2`.  The replacement has length `i + 1 + (|w| - j)`,
which is `< |w|` exactly when `i + 1 < j`.  Had adjacency been possible the
collapse would have been length-preserving and the argument would fail, so the
`i + 2 ≤ j` hypothesis is doing real work and is not slack.

## The three things the replacement has to keep

* **Value.**  The prefix spells the way to `vertex i`, the new letter spells the
  difference, and the suffix spells the way from `vertex j` to the end; the
  middle two compose to the way from `vertex i` to `vertex j`.
* **Admissibility.**  Prefix and suffix letters come from `w`; the new letter is
  a base letter, so it is admissible as soon as `g` lies in the base --- which is
  what "connected" supplies, the family having been swallowed by the base at the
  point where this is used.
* **Avoidance.**  This is the clause that could have failed and does not.  A base
  letter never traverses `Γ_{H_λ}`, so the new letter is free; and the splice
  **lands on the same vertex** the original word was at after `j` letters, so the
  suffix's avoidance transports with no change of basepoint.  That is the whole
  reason the collapse is legitimate, and it is why the replacement is stated with
  `g` pinned to `(vertex i)⁻¹ * vertex j` rather than as an arbitrary element of
  the base.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Splice

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  The replacement word -/

/-- **`w` with everything between positions `i` and `j` replaced by one base
letter.**  The letter is supplied rather than computed, so that the lemmas below
can pin it to the difference of the two vertices exactly where that is what makes
them true. -/
def spliceWord (w : List (RelLetter G Λ)) (i j : ℕ) (g : G) :
    List (RelLetter G Λ) :=
  w.take i ++ RelLetter.base g :: w.drop j

omit [Group G] in
/-- **The replacement is shorter by `j - i - 1`.**

`spliceWord` is built from `take`, `++` and `drop` and multiplies nothing, so
neither it nor its length carries the group structure; every other lemma here
does, `listVal` requiring `[Group G]` by its own signature and `vertex`
multiplying at each step. -/
theorem length_spliceWord (w : List (RelLetter G Λ)) {i : ℕ} (hi : i ≤ w.length)
    (j : ℕ) (g : G) :
    (spliceWord w i j g).length = i + 1 + (w.length - j) := by
  show (w.take i ++ RelLetter.base g :: w.drop j).length = _
  rw [List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

/-- **The prefix spells the way to its endpoint.**  Read off
`vertex_eq_mul_listVal_take` at the basepoint. -/
theorem listVal_take_eq_vertex (w : List (RelLetter G Λ)) (i : ℕ) :
    RelLetter.listVal (w.take i) = vertex (1 : G) w i := by
  rw [vertex_eq_mul_listVal_take, one_mul]

/-- **The suffix spells the way from its start to the end.** -/
theorem vertex_mul_listVal_drop (w : List (RelLetter G Λ)) {j : ℕ}
    (hj : j ≤ w.length) :
    vertex (1 : G) w j * RelLetter.listVal (w.drop j) = RelLetter.listVal w := by
  have hkey := vertex_drop_eq w (1 : G) j (w.length - j)
  have harg : j + (w.length - j) = w.length := by omega
  rw [harg] at hkey
  have hd : vertex (1 : G) (w.drop j) (w.length - j)
      = RelLetter.listVal (w.drop j) := by
    have hlen : w.length - j = (w.drop j).length := by rw [List.length_drop]
    rw [hlen, vertex_eq_mul_listVal_take, List.take_length, one_mul]
  have hw : vertex (1 : G) w w.length = RelLetter.listVal w := by
    rw [vertex_eq_mul_listVal_take, List.take_length, one_mul]
  rw [hd, hw] at hkey
  exact hkey

/-! ## 2.  The three clauses the replacement keeps -/

/-- **Value.**  The collapse spells what the original spelled. -/
theorem listVal_spliceWord (w : List (RelLetter G Λ)) (i : ℕ) {j : ℕ}
    (hj : j ≤ w.length) :
    RelLetter.listVal
        (spliceWord w i j ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j))
      = RelLetter.listVal w := by
  show RelLetter.listVal (w.take i
      ++ RelLetter.base ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j)
        :: w.drop j) = _
  rw [listVal_append, listVal_cons, listVal_take_eq_vertex]
  show vertex (1 : G) w i * (((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j)
      * RelLetter.listVal (w.drop j)) = RelLetter.listVal w
  rw [← vertex_mul_listVal_drop w hj]
  group

/-- **Admissibility.**  Prefix and suffix letters are the original's; the new
letter is admissible as soon as it lies in the base. -/
theorem isLetter_spliceWord {D : RelGenSet G Λ} {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (i j : ℕ) {g : G} (hg : g ∈ D.base) :
    ∀ a ∈ spliceWord w i j g, D.IsLetter a := by
  intro a ha
  rcases List.mem_append.mp ha with hpre | hsuf
  · exact hlet a (List.take_subset i w hpre)
  · rcases List.mem_cons.mp hsuf with rfl | hd
    · exact hg
    · exact hlet a (List.drop_subset j w hd)

/-- **Avoidance.**  The new letter is a base letter, so it traverses no
`Γ_{H_λ}`; and the splice lands on the vertex the original reached after `j`
letters, so the suffix keeps its basepoint and with it its avoidance. -/
theorem avoidsFrom_spliceWord {H : Λ → Subgroup G} {lam : Λ}
    {w : List (RelLetter G Λ)} (hav : AvoidsFrom H lam w 1) (i j : ℕ) :
    AvoidsFrom H lam
      (spliceWord w i j ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j)) 1 := by
  show AvoidsFrom H lam (w.take i
      ++ RelLetter.base ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j)
        :: w.drop j) 1
  rw [avoidsFrom_append]
  refine ⟨avoidsFrom_take H lam 1 w i hav, ?_⟩
  rw [listVal_take_eq_vertex, one_mul]
  refine ⟨fun hc => hc.1, ?_⟩
  show AvoidsFrom H lam (w.drop j)
    (vertex (1 : G) w i * ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j))
  have hvert : vertex (1 : G) w i
      * ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j) = vertex (1 : G) w j := by
    group
  rw [hvert]
  exact avoidsFrom_drop H lam 1 w j hav

/-! ## 3.  A shortest word has no connected pair -/

/-- **Minimality forbids a connected pair.**

If two positions of a shortest admissible avoiding word are separated by at least
two letters and their vertices differ by an element of the base, the collapse
above is a strictly shorter word with the same three properties --- which
minimality forbids.

Stated over an arbitrary element of the base rather than over a family member,
because at the point of use the family in question has been moved into the base:
that is exactly the enlargement Lemma `ee` performs, and it is what makes the
replacement letter admissible. -/
theorem not_mem_base_of_minimal {D : RelGenSet G Λ} {lam : Λ} {h : G}
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hval : RelLetter.listVal w = h) (hav : AvoidsFrom D.fam lam w 1)
    (hmin : ∀ v : List (RelLetter G Λ), (∀ a ∈ v, D.IsLetter a) →
      RelLetter.listVal v = h → AvoidsFrom D.fam lam v 1 → w.length ≤ v.length)
    {i j : ℕ} (hij : i + 2 ≤ j) (hjw : j ≤ w.length) :
    (vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j ∉ D.base := by
  intro hg
  have hi : i ≤ w.length := by omega
  have hlen := length_spliceWord w hi j
    ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j)
  have hle := hmin
    (spliceWord w i j ((vertex (1 : G) w i)⁻¹ * vertex (1 : G) w j))
    (isLetter_spliceWord hlet i j hg)
    (by rw [listVal_spliceWord w i hjw]; exact hval)
    (avoidsFrom_spliceWord hav i j)
  omega

end Splice

end OsinComponents
end GGT
end GroupApproximation
