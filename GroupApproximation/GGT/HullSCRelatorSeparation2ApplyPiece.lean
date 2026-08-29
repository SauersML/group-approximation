import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNarrowPair

/-!
# From a piece to a closed case

The last link.  Above it sit the closers, each of which wants a match already
found; below it sit `HullSC.exists_block_of_long_prefix_rotate`, which finds a
block letter in any window longer than the base part, and
`GGT.OsinComponents.exists_deep_match_hyp`, which matches it across.  A PIECE
goes in --- a prefix longer than `|p|` --- and the identity `RelWord.IsPiece`
excludes comes out.

Three steps, and only the middle one is not bookkeeping: the window count puts a
block letter in the piece, the design's depth clause makes its span deep, and a
deep component is not isolated, hence matched.

One shape is worth pointing at.  The two same-side exclusions are quantified
over the SUBGROUP INDEX as well as the position, because the index is not known
until the block is found --- the window count returns which of the two
subgroups the letter it found belongs to, and the exclusions have to be
available for whichever it is.  Writing them at a fixed index would make the
statement unusable exactly where it is applied.

The polygon's output and the matching step are section variables: they are the
same in every case, and repeating them would be the bulk of the file.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Piece

variable {G : Type u} [Group G] {D : GGT.RelGenSet G Bool} {a : Bool → G}
  {eps rho Cm bn : ℕ} {ms : List ℕ}

variable
  (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
  (hmatch : GGT.OsinComponents.DeepMatchOutput D Cm bn)

include hpair hmatch in
/-- **The aligned case, from a piece.**  Both members rotations of the
relator. -/
theorem listVal_conj_of_alignedMatch_piece (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho) (hms : 0 < ms.length)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hlong : p.length < u.length)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hqg : ∀ t : ℕ, t < 4 → ∀ z y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ z → z ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - z : ℕ) : ℝ) / 1 - (bn : ℝ)
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hqside : ∀ (t : Bool) (d i' : ℕ), i' ≤ u.length → i' ≠ d →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  obtain ⟨d, b, e, hd, he, hletd⟩ :=
    exists_block_of_long_prefix_rotate (h₀ := a false) (h₁ := a true) (c := c)
      hms hlong
  have hlu : u[d]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)) := by
    rw [← hletd, hw]
    exact (List.getElem?_append_left hd).symm
  have hspan : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d + 1) = a b ^ e := by
    rw [span_eq_val_of_getElem? hlu]
    show (if b then a true else a false) ^ e = a b ^ e
    rw [ite_apply_eq a b]
  have hdeepspan : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d + 1) ∉ D.relBall b rho := by
    rw [hspan]
    exact (hdeep e he b).1
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hd hletd
  have hpolyq := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon py u pz u' D
    hlet4 hclose hqg
  obtain ⟨k, hk0, hk, ⟨x, hx⟩, h, hh, hconn⟩ :=
    hmatch b rho py u pz u' d hrho hclose hpy hpz hpz0 hpolyq hcompu hdeepspan
      (hqside b d)
  exact listVal_conj_of_alignedMatch_found hnodup hinj hsep hdiag hpair
    hp0 hw hw' hd hk0 hk he hletd hx hh hconn hpy hpz hpy0 hpz0 hlet4 hclose
    hqg (hqside b d) (hsside b k)

include hpair hmatch in
/-- **The mirrored aligned case, from a piece.**

Both members rotations of the formal inverse.  The window count is the mirrored
one --- in the formal inverse the run comes first --- the letter it finds
carries the inverse of a power, so the depth clause is spent on its second half
rather than its first, and the mirrored closer finishes. -/
theorem listVal_conj_of_mirroredAlignedMatch_piece (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho) (hms : 0 < ms.length)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    (hlong : p.length < u.length)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hqg : ∀ t : ℕ, t < 4 → ∀ z y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ z → z ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - z : ℕ) : ℝ) / 1 - (bn : ℝ)
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hqside : ∀ (t : Bool) (d i' : ℕ), i' ≤ u.length → i' ≠ d →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  obtain ⟨d, b, e, hd, he, hletd⟩ :=
    exists_block_of_long_prefix_rotate_revInv (h₀ := a false) (h₁ := a true)
      (c := c) hms hlong
  have hlu : u[d]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)) := by
    rw [← hletd, hw]
    exact (List.getElem?_append_left hd).symm
  have hspan : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d + 1) = (a b ^ e)⁻¹ := by
    rw [span_eq_val_of_getElem? hlu]
    show ((if b then a true else a false) ^ e)⁻¹ = (a b ^ e)⁻¹
    rw [ite_apply_eq a b]
  have hdeepspan : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d + 1) ∉ D.relBall b rho := by
    rw [hspan]
    exact (hdeep e he b).2
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw hd hletd
  have hpolyq := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon py u pz u' D
    hlet4 hclose hqg
  obtain ⟨k, hk0, hk, ⟨x, hx⟩, h, hh, hconn⟩ :=
    hmatch b rho py u pz u' d hrho hclose hpy hpz hpz0 hpolyq hcompu hdeepspan
      (hqside b d)
  exact listVal_conj_of_mirroredAlignedMatch_found hnodup hinj hsymm hsep hdiag
    hpair hp0 hw hw' hd hk0 hk he hletd hx hh hconn hpy hpz hpy0 hpz0 hlet4
    hclose hqg (hqside b d) (hsside b k)

end Piece

end HullSC
end GroupApproximation
