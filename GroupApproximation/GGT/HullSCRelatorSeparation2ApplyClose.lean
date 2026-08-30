import GroupApproximation.GGT.HullSCRelatorSeparation2Apply

/-!
# One match, closed

The polygon delivers its two gaps in the vocabulary of the SIDES of the
quadrilateral --- the matched prefixes `u`, `u'` --- and the closers read the
members of the symmetrized closure that those prefixes sit in.  Reconciling the
two is one step in each direction and no more:

* a letter of a prefix is the letter of the word at the same index
  (`List.getElem?_append_left`), which is what carries the two block letters
  from the closure member into the side;
* a vertex of a word inside its first block is a vertex of that block
  (`HullSC.vertex_mul_gap`), which is what carries the vertex relation back.

With those, `HullSC.conj_of_matchedPair_letters` turns the gaps into the
connector relation the design reads, and the aligned closers apply.  The `y` in
the conclusion is the quadrilateral's own first side throughout, which is what
`RelWord.IsPiece` excludes.

Both aligned cases are here.  The mixed cases need no reconciliation of this
kind --- they consume the connector relation alone and never the vertex
relation --- so they are applied directly from
`GGT.OsinComponents.exists_eps_matchedPair`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Close

variable {G : Type u} [Group G]

/-- **The aligned case, from the polygon's output at a matched pair.**

Both members rotations of the relator, the two gaps named as the polygon names
them, and the two prefixes the quadrilateral's long sides. -/
theorem listVal_conj_of_alignedMatch_pair {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hiR : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hjR : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hiu : i + 1 ≤ u.length) (hju : j + 1 ≤ u'.length)
    (hxb : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
      ∈ D.relBall b eps)
    (hx'b : (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' (j + 1) ∈ D.relBall b eps)
    (hx'1 : (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' (j + 1) = 1)
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hlet' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f))) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hlu : u[i]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ e)) := by
    rw [← hlet, hw]
    exact (List.getElem?_append_left (by omega)).symm
  have hlu' : u'[j]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ f)) := by
    rw [← hlet', hw']
    exact (List.getElem?_append_left (by omega)).symm
  have hspan := conj_of_matchedPair_letters (py := py) hlu hlu'
  rw [ite_apply_eq a b] at hspan
  have hvert := vertex_mul_gap (y := GGT.RelLetter.listVal py) hw hw'
    (by omega : i ≤ u.length) (by omega : j ≤ u'.length)
  exact listVal_conj_of_alignedMatch_gap hnodup hinj hsep hiR hjR he hf
    hxb hx'b hspan hx'1 hlet hlet' hvert

/-- **The mirrored aligned case, from the polygon's output at a matched pair.**

Both members rotations of the formal inverse.  The letters carry inverses, so
the connector relation does, and the mirrored closer is the one that applies;
nothing else changes. -/
theorem listVal_conj_of_mirroredAlignedMatch_pair {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hiR : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hjR : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    (hiu : i + 1 ≤ u.length) (hju : j + 1 ≤ u'.length)
    (hxb : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
      ∈ D.relBall b eps)
    (hx'b : (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' (j + 1) ∈ D.relBall b eps)
    (hx1 : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u i) = 1)
    (hlet : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)))
    (hlet' : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹))) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hlu : u[i]? = some (GGT.RelLetter.comp b
      (((if b then a true else a false) ^ e)⁻¹)) := by
    rw [← hlet, hw]
    exact (List.getElem?_append_left (by omega)).symm
  have hlu' : u'[j]? = some (GGT.RelLetter.comp b
      (((if b then a true else a false) ^ f)⁻¹)) := by
    rw [← hlet', hw']
    exact (List.getElem?_append_left (by omega)).symm
  have hspan := conj_of_matchedPair_letters (py := py) hlu hlu'
  rw [ite_apply_eq a b] at hspan
  have hvert := vertex_mul_gap (y := GGT.RelLetter.listVal py) hw hw'
    (by omega : i ≤ u.length) (by omega : j ≤ u'.length)
  exact listVal_conj_of_mirroredAlignedMatch_gap hnodup hinj hsymm hsep
    hiR hjR he hf hxb hx'b hspan hx1 hlet hlet' hvert

end Close

end HullSC
end GroupApproximation
