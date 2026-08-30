import GroupApproximation.GGT.HullSCRelatorSeparation2OtherArc
import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot

/-!
# The polygon, applied: the three shapes of step (c)

The quadrilateral Olshanskii's step (a) is run on is the one the long match
gives: `py ++ u ++ pz ++ revWord u'`, with `u` a prefix of one member of the
symmetrized closure, `u'` a prefix of the other, and `py`, `pz` base spellings
of the piece's two connectors.  Its two long sides are the matched prefixes, not
single letters, and the matched pair is a block letter of `u` against a block
letter of `u'`.

`GGT.OsinComponents.two_block_conj_named` puts both gaps of such a pair in a
relative ball and, unlike the existential form, keeps their names:

* `x  = (vertex 1 u' j)⁻¹ * (listVal py * vertex 1 u i)`, start to start;
* `x' = (listVal py * vertex 1 u (i+1))⁻¹ * vertex 1 u' (j+1)`, end to end.

This module spends that output.  Two small lemmas turn it into what the closers
read, and then the cases.

* `conj_of_matchedPair_letters` --- the gap identity with the two spans read as
  the two block letters' values.  Over the alternating relator a component of
  the run spans one letter, so `k = i + 1` and `l = j + 1`, and the spans ARE
  the letters.
* `vertex_mul_gap` --- the vertex relation the join consumes, with the first gap
  by name.  It is an identity: `y * vertex 1 w i = vertex 1 w' j * x` holds for
  `x` the start-to-start gap whatever `y` is, the two prefixes carrying the same
  vertices as the members they sit in.  What the design adds is `x = 1`, and
  then it says `y * vertex 1 w i = vertex 1 w' j`.

## The cases

* `listVal_conj_of_alignedMatch_gap` --- both members rotations of the relator.
* `listVal_conj_of_mirroredAlignedMatch_gap` --- both rotations of the formal
  inverse.
* `false_of_mixedMatch_gap_inv` --- the mixed order in which the member carrying
  the direct powers is the SECOND one.  The gap identity then runs the wrong way
  for the separation clause, and inverting it puts it back, both gaps staying in
  the ball because relative balls are closed under inversion.

The other mixed order needs no lemma at all: there the gap identity is
`x · a_b^e · x' = (a_b^f)⁻¹` on the nose, which is what
`HullSC.false_of_span_mixed` takes, so the composition applies that theorem to
the polygon's output unchanged.

All three are stated over the two gaps as GROUP ELEMENTS rather than over words
spelling them.  That is deliberate: the gaps of the long quadrilateral are
elements of the subgroup, not base words, and nothing below reads them as
anything but elements.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Gap

variable {G : Type u} [Group G]

/-- **The gap identity, with the two spans read as letters.**

`GGT.OsinComponents.block_span_conj` is an identity between the two gaps and the
two component spans; over the alternating relator each component spans one
letter, so the spans are the letters' values. -/
theorem conj_of_matchedPair_letters {nu : Bool}
    {py w w' : List (GGT.RelLetter G Bool)} {i j : ℕ} {vq vs : G}
    (hw : w[i]? = some (GGT.RelLetter.comp nu vq))
    (hw' : w'[j]? = some (GGT.RelLetter.comp nu vs)) :
    ((GGT.OsinComponents.vertex (1 : G) w' j)⁻¹ *
          (GGT.RelLetter.listVal py *
            GGT.OsinComponents.vertex (1 : G) w i)) * vq *
        ((GGT.RelLetter.listVal py *
            GGT.OsinComponents.vertex (1 : G) w (i + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) w' (j + 1))
      = vs := by
  have h := GGT.OsinComponents.block_span_conj py w w' i (i + 1) j (j + 1)
  rw [span_eq_val_of_getElem? hw, span_eq_val_of_getElem? hw'] at h
  exact h

/-- **The vertex relation, with the first gap by name.**

An identity, and the only place the two prefixes are used: a vertex of a word
inside its first block is a vertex of that block. -/
theorem vertex_mul_gap {w w' pre pre' : List (GGT.RelLetter G Bool)} {i j : ℕ}
    {y : G} {t t' : List (GGT.RelLetter G Bool)} (hw : w = pre ++ t)
    (hw' : w' = pre' ++ t') (hi : i ≤ pre.length) (hj : j ≤ pre'.length) :
    y * GGT.OsinComponents.vertex (1 : G) w i
      = GGT.OsinComponents.vertex (1 : G) w' j *
        ((GGT.OsinComponents.vertex (1 : G) pre' j)⁻¹ *
          (y * GGT.OsinComponents.vertex (1 : G) pre i)) := by
  subst hw
  subst hw'
  rw [GGT.OsinComponents.vertex_append_of_le pre t 1 i hi,
    GGT.OsinComponents.vertex_append_of_le pre' t' 1 j hj]
  group

end Gap

section Cases

variable {G : Type u} [Group G]

/-- **The aligned case, from the polygon's output.**

Both members rotations of the relator.  The design makes both gaps trivial, the
vertex relation loses its right factor, and the join gives the identity
`RelWord.IsPiece` excludes, with `y` the quadrilateral's own first side. -/
theorem listVal_conj_of_alignedMatch_gap {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {xg xg' y : G}
    (hxb : xg ∈ D.relBall b eps) (hrb : xg' ∈ D.relBall b eps)
    (hgap : xg * a b ^ e * xg' = a b ^ f)
    (hxg'1 : xg' = 1)
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hlet' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f)))
    (hvert : y * GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) i
        = GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c') j * xg) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = y * GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) * y⁻¹ := by
  obtain ⟨hef, hx1, -⟩ :=
    trivial_connector_of_alignedMatch_ball hsep he hf hxb hrb hgap hxg'1
  rw [hx1, mul_one] at hvert
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  exact listVal_conj_of_alignedTrivial hinj' hnodup hi hj hef hlet hlet' hvert

/-- **The mirrored aligned case, from the polygon's output.**

Both members rotations of the formal inverse.  Their letters carry inverses, so
the gap identity does too, and the mirrored form of the trivial-connector step
is what applies; the rotation identity then comes from the mirrored position
lemma rather than the direct one. -/
theorem listVal_conj_of_mirroredAlignedMatch_gap {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {xg xg' y : G}
    (hxb : xg ∈ D.relBall b eps) (hrb : xg' ∈ D.relBall b eps)
    (hgap : xg * (a b ^ e)⁻¹ * xg' = (a b ^ f)⁻¹)
    (hxg1 : xg = 1)
    (hlet : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)))
    (hlet' : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)))
    (hvert : y * GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c) i
        = GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c') j * xg) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = y * GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) * y⁻¹ := by
  obtain ⟨hef, hx1, -⟩ :=
    trivial_connector_of_mirroredAlignedMatch_ball hsymm hsep he hf hxb
      hrb hgap hxg1
  rw [hx1, mul_one] at hvert
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  refine listVal_conj_of_rotate_eq_of_vertex_eq ?_ ?_
    (rotate_eq_of_position_eq
      (RelWord.revInv (relatorWord₂ p (a false) (a true) ms))
      (position_eq_of_alignedMatch_revInv hinj' hnodup hi hj hef hlet hlet'))
    hvert
  · rw [List.length_rotate]
    omega
  · rw [List.length_rotate]
    omega

/-- **The mixed order in which the formal inverse comes first.**

The member carrying the direct powers is the second one, so the gap identity
reads `x · (a_b^f)⁻¹ · x' = a_b^e` --- the mirrored half of the separation
clause with its two sides exchanged.  Inverting it restores the shape the clause
is stated in, and `HullSC.inv_mem_relBall` keeps both gaps in the ball, after
which the gap estimate closes the case exactly as in the other order. -/
theorem false_of_mixedMatch_gap_inv {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i₁ i₂ j₁ j₂ gapSlack : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hj₂ : j₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₂ : Bool} {e₁ f₁ e₂ f₂ : ℕ}
    (he₁ : e₁ ∈ ms) (hf₁ : f₁ ∈ ms) (he₂ : e₂ ∈ ms) (hf₂ : f₂ ∈ ms)
    {xg₁ xg₁' xg₂ xg₂' : G}
    (hx₁ : xg₁ ∈ D.relBall b₁ eps) (hr₁ : xg₁' ∈ D.relBall b₁ eps)
    (hx₂ : xg₂ ∈ D.relBall b₂ eps) (hr₂ : xg₂' ∈ D.relBall b₂ eps)
    (hgap₁ : xg₁ * (a b₁ ^ f₁)⁻¹ * xg₁' = a b₁ ^ e₁)
    (hgap₂ : xg₂ * (a b₂ ^ f₂)⁻¹ * xg₂' = a b₂ ^ e₂)
    (hl₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c')[i₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then a true else a false) ^ e₁)))
    (hm₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[j₁]?
      = some (GGT.RelLetter.comp b₁
          (((if b₁ then a true else a false) ^ f₁)⁻¹)))
    (hl₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c')[i₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then a true else a false) ^ e₂)))
    (hm₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[j₂]?
      = some (GGT.RelLetter.comp b₂
          (((if b₂ then a true else a false) ^ f₂)⁻¹)))
    (hcount : j₂ - j₁ ≤ i₂ - i₁ + gapSlack)
    (hsmall : 2 * (i₂ - i₁) + gapSlack
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hc₁ : xg₁⁻¹ * a b₁ ^ e₁ * xg₁'⁻¹ = (a b₁ ^ f₁)⁻¹ := by
    rw [← hgap₁]
    group
  have hc₂ : xg₂⁻¹ * a b₂ ^ e₂ * xg₂'⁻¹ = (a b₂ ^ f₂)⁻¹ := by
    rw [← hgap₂]
    group
  exact false_of_span_mixed hnodup hinj hsep hi₂ hj₂ hii hjj he₁ hf₁ he₂ hf₂
    (inv_mem_relBall hsymm hx₁) (inv_mem_relBall hsymm hr₁)
    (inv_mem_relBall hsymm hx₂) (inv_mem_relBall hsymm hr₂)
    hl₁ hm₁ hl₂ hm₂ hc₁ hc₂ hcount hsmall

end Cases

end HullSC
end GroupApproximation
