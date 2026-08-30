import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMixedInv
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNarrowPair
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyTwoBlock
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyW4Match

/-!
# From a piece to a closed case

The last link.  Above it sit the closers, each of which wants a match already
found; below it sit the window counts, which find block letters in any window
longer than the base part, and `GGT.OsinComponents.exists_deep_match_hyp`,
which matches them across.  A PIECE goes in --- a prefix longer than `|p|` ---
and the identity `RelWord.IsPiece` excludes comes out.

Three steps, and only the middle one is not bookkeeping: the window count puts a
block letter in the piece, the design's depth clause makes its span deep, and a
deep component is not isolated, hence matched.

The two aligned cases run all three inside `HullSC.exists_match_with_trivialGap`
and its mirrored twin, which absorb the finder and the matching step together
and return the (W4) equation the closers take in place of the old design clause
about commutation.  That is what fixes their length clauses: the step reads
three CONSECUTIVE block letters, so the piece is longer than `|p| + 4` and the
exponent list is at least five.

One shape is worth pointing at.  The two same-side exclusions are quantified
over the SUBGROUP INDEX as well as the position, because the index is not known
until the block is found --- the window count returns which of the two
subgroups the letter it found belongs to, and the exclusions have to be
available for whichever it is.  Writing them at a fixed index would make the
statement unusable exactly where it is applied.

The mixed cases take two block letters rather than one, from
`HullSC.exists_two_blocks_of_long_prefix_rotate`, since they close by comparing
two matches rather than by rewriting one.  The two length constants of the
construction are what that count costs, and both are stated in those two
theorems rather than left to the caller.

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
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho) (hms : 5 ≤ ms.length)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hlong : p.length + 4 < u.length)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hslet : ∀ z ∈ u', D.IsLetter z)
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
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  obtain ⟨d, b, e, k, hd, he, hletd, hk0, hk, ⟨x, hx⟩, ⟨h, hh, hconn⟩,
      hgap⟩ :=
    exists_match_with_trivialGap hdisj hnodup hinj hsep hdeep hrho hms hpair
      hmatch hp0 hw hw' hlong hpy hpz hpy0 hpz0 hlet4 hslet hclose hqg hqside
      hsside
  exact listVal_conj_of_alignedMatch_found hnodup hinj hsep hpair
    hp0 hw hw' hd hk0 hk he hletd hx hh hconn hgap hpy hpz hpy0 hpz0 hlet4
    hclose hqg (hqside b d) (hsside b k)

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
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho) (hms : 5 ≤ ms.length)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    (hlong : p.length + 4 < u.length)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hslet : ∀ z ∈ u', D.IsLetter z)
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
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  obtain ⟨d, b, e, k, hd, he, hletd, hk0, hk, ⟨x, hx⟩, ⟨h, hh, hconn⟩,
      hgap⟩ :=
    exists_match_with_trivialGap_revInv hdisj hnodup hinj hsymm hsep hdeep hrho
      hms hpair hmatch hp0 hw hw' hlong hpy hpz hpy0 hpz0 hlet4 hslet hclose
      hqg hqside hsside
  exact listVal_conj_of_mirroredAlignedMatch_found hnodup hinj hsymm hsep
    hpair hp0 hw hw' hd hk0 hk he hletd hx hh hconn hgap hpy hpz hpy0 hpz0
    hlet4 hclose hqg (hqside b d) (hsside b k)

include hpair hmatch in
/-- **The first mixed case, from a piece.**  The piece is a rotation of the
relator and the other member a rotation of the formal inverse.

Two block letters rather than one.  A mixed case does not close by rewriting a
single match: two matches are found and compared, and it is the comparison
that fails.  So the window count is run at the pinning separation, and that is
what fixes the two design constants.  The piece is longer than
`|p| + blockSeparation + 1`, which is what `B` is taken to be; and the exponent
list is longer than `|p| + 5 * blockSeparation + 2`, which is what the closer's
length clause is discharged from, the second offset being at most
`|p| + blockSeparation + 1` and the closer asking for `2 (d₂ - d₁)` and three
separations to fit inside the relator. -/
theorem false_of_mixedMatch_piece (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    {bb : ℝ} {cnt epsPin : ℕ}
    (hlongp : p.length + blockSeparation p cnt epsPin + 1 < u.length)
    (hmslong : p.length + 5 * blockSeparation p cnt epsPin + 2 < ms.length)
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
    (hqlet : ∀ z ∈ u, D.IsLetter z) (hslet : ∀ z ∈ u', D.IsLetter z)
    (hqgq : ∀ x y : ℕ, x ≤ y → y ≤ u.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u x)
              (GGT.OsinComponents.vertex (1 : G) u y) : ℕ) : ℝ))
    (hqgs : ∀ x y : ℕ, x ≤ y → y ≤ u'.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u' x)
              (GGT.OsinComponents.vertex (1 : G) u' y) : ℕ) : ℝ))
    (hB : bb ≤ ((blockConst p cnt : ℕ) : ℝ))
    (hple : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ epsPin)
    (hqside : ∀ (t : Bool) (d i' : ℕ), i' ≤ u.length → i' ≠ d →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) : False := by
  have hmsk : blockSeparation p cnt epsPin + 2 ≤ ms.length := by omega
  obtain ⟨d₁, d₂, b₁, b₂, e₁, e₂, hsepn, hd₂, hd₂P, he₁, he₂, hletd₁,
      hletd₂⟩ :=
    exists_two_blocks_of_long_prefix_rotate (h₀ := a false) (h₁ := a true)
      (c := c) hmsk hlongp
  have hd₁ : d₁ < u.length := by omega
  have hlu₁ : u[d₁]? = some (GGT.RelLetter.comp b₁
      ((if b₁ then a true else a false) ^ e₁)) := by
    rw [← hletd₁, hw]
    exact (List.getElem?_append_left hd₁).symm
  have hlu₂ : u[d₂]? = some (GGT.RelLetter.comp b₂
      ((if b₂ then a true else a false) ^ e₂)) := by
    rw [← hletd₂, hw]
    exact (List.getElem?_append_left hd₂).symm
  have hspan₁ : (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₁ + 1) = a b₁ ^ e₁ := by
    rw [span_eq_val_of_getElem? hlu₁]
    show (if b₁ then a true else a false) ^ e₁ = a b₁ ^ e₁
    rw [ite_apply_eq a b₁]
  have hspan₂ : (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₂ + 1) = a b₂ ^ e₂ := by
    rw [span_eq_val_of_getElem? hlu₂]
    show (if b₂ then a true else a false) ^ e₂ = a b₂ ^ e₂
    rw [ite_apply_eq a b₂]
  have hdeep₁ : (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₁ + 1) ∉ D.relBall b₁ rho := by
    rw [hspan₁]
    exact (hdeep e₁ he₁ b₁).1
  have hdeep₂ : (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₂ + 1) ∉ D.relBall b₂ rho := by
    rw [hspan₂]
    exact (hdeep e₂ he₂ b₂).1
  have hcomp₁ : GGT.OsinComponents.IsComp b₁ u d₁ (d₁ + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hd₁ hletd₁
  have hcomp₂ : GGT.OsinComponents.IsComp b₂ u d₂ (d₂ + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hd₂ hletd₂
  have hpolyq := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon py u pz u' D
    hlet4 hclose hqg
  obtain ⟨k₁, hk01, hk₁, ⟨x₁, hx₁⟩, g₁, hg₁, hconn₁⟩ :=
    hmatch b₁ rho py u pz u' d₁ hrho hclose hpy hpz hpz0 hpolyq hcomp₁
      hdeep₁ (hqside b₁ d₁)
  obtain ⟨k₂, hk02, hk₂, ⟨x₂, hx₂⟩, g₂, hg₂, hconn₂⟩ :=
    hmatch b₂ rho py u pz u' d₂ hrho hclose hpy hpz hpz0 hpolyq hcomp₂
      hdeep₂ (hqside b₂ d₂)
  have hRlen : (relatorWord₂ p (a false) (a true) ms).length
      = p.length + ms.length := length_relatorWord₂ p (a false) (a true) ms
  exact false_of_mixedMatch_found hnodup hinj hsep hpair hp0 hw hw' hpy hpz
    hpy0 hpz0 hlet4 hclose hqg hqlet hslet hqgq hqgs hB hple he₁ he₂ hd₁ hd₂
    hk01 hk02 hk₁ hk₂ hletd₁ hletd₂ hx₁ hx₂ hg₁ hg₂ hconn₁ hconn₂
    (hqside b₁ d₁) (hqside b₂ d₂) (hsside b₁ k₁) (hsside b₂ k₂) hsepn
    (by omega)

include hpair hmatch in
/-- **The second mixed case, from a piece.**  The piece is a rotation of the
formal inverse and the other member a rotation of the relator.

The mirrored window count, the depth clause spent on its second half, and the
inverted closer, whose length clause asks for three separations rather than
one.  The exponent list's bound is stated at the larger of the two so that one
number serves both mixed cases. -/
theorem false_of_mixedMatch_piece_inv (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    {bb : ℝ} {cnt epsPin : ℕ}
    (hlongp : p.length + blockSeparation p cnt epsPin + 1 < u.length)
    (hmslong : p.length + 5 * blockSeparation p cnt epsPin + 2 < ms.length)
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
    (hqlet : ∀ z ∈ u, D.IsLetter z) (hslet : ∀ z ∈ u', D.IsLetter z)
    (hqgq : ∀ x y : ℕ, x ≤ y → y ≤ u.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u x)
              (GGT.OsinComponents.vertex (1 : G) u y) : ℕ) : ℝ))
    (hqgs : ∀ x y : ℕ, x ≤ y → y ≤ u'.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u' x)
              (GGT.OsinComponents.vertex (1 : G) u' y) : ℕ) : ℝ))
    (hB : bb ≤ ((blockConst p cnt : ℕ) : ℝ))
    (hple : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ epsPin)
    (hqside : ∀ (t : Bool) (d i' : ℕ), i' ≤ u.length → i' ≠ d →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ), m ≤ u'.length → m ≠ k →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) : False := by
  have hmsk : blockSeparation p cnt epsPin + 2 ≤ ms.length := by omega
  obtain ⟨d₁, d₂, b₁, b₂, f₁, f₂, hsepn, hd₂, hd₂P, hf₁, hf₂, hletd₁,
      hletd₂⟩ :=
    exists_two_blocks_of_long_prefix_rotate_revInv (h₀ := a false)
      (h₁ := a true) (c := c) hmsk hlongp
  have hd₁ : d₁ < u.length := by omega
  have hlu₁ : u[d₁]? = some (GGT.RelLetter.comp b₁
      (((if b₁ then a true else a false) ^ f₁)⁻¹)) := by
    rw [← hletd₁, hw]
    exact (List.getElem?_append_left hd₁).symm
  have hlu₂ : u[d₂]? = some (GGT.RelLetter.comp b₂
      (((if b₂ then a true else a false) ^ f₂)⁻¹)) := by
    rw [← hletd₂, hw]
    exact (List.getElem?_append_left hd₂).symm
  have hspan₁ : (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₁ + 1) = (a b₁ ^ f₁)⁻¹ := by
    rw [span_eq_val_of_getElem? hlu₁]
    show ((if b₁ then a true else a false) ^ f₁)⁻¹ = (a b₁ ^ f₁)⁻¹
    rw [ite_apply_eq a b₁]
  have hspan₂ : (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₂ + 1) = (a b₂ ^ f₂)⁻¹ := by
    rw [span_eq_val_of_getElem? hlu₂]
    show ((if b₂ then a true else a false) ^ f₂)⁻¹ = (a b₂ ^ f₂)⁻¹
    rw [ite_apply_eq a b₂]
  have hdeep₁ : (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₁ + 1) ∉ D.relBall b₁ rho := by
    rw [hspan₁]
    exact (hdeep f₁ hf₁ b₁).2
  have hdeep₂ : (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d₂ + 1) ∉ D.relBall b₂ rho := by
    rw [hspan₂]
    exact (hdeep f₂ hf₂ b₂).2
  have hcomp₁ : GGT.OsinComponents.IsComp b₁ u d₁ (d₁ + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw hd₁ hletd₁
  have hcomp₂ : GGT.OsinComponents.IsComp b₂ u d₂ (d₂ + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw hd₂ hletd₂
  have hpolyq := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon py u pz u' D
    hlet4 hclose hqg
  obtain ⟨k₁, hk01, hk₁, ⟨x₁, hx₁⟩, g₁, hg₁, hconn₁⟩ :=
    hmatch b₁ rho py u pz u' d₁ hrho hclose hpy hpz hpz0 hpolyq hcomp₁
      hdeep₁ (hqside b₁ d₁)
  obtain ⟨k₂, hk02, hk₂, ⟨x₂, hx₂⟩, g₂, hg₂, hconn₂⟩ :=
    hmatch b₂ rho py u pz u' d₂ hrho hclose hpy hpz hpz0 hpolyq hcomp₂
      hdeep₂ (hqside b₂ d₂)
  have hRlen : (relatorWord₂ p (a false) (a true) ms).length
      = p.length + ms.length := length_relatorWord₂ p (a false) (a true) ms
  exact false_of_mixedMatch_found_inv hnodup hinj hsymm hsep hpair hp0 hw hw'
    hpy hpz hpy0 hpz0 hlet4 hclose hqg hqlet hslet hqgq hqgs hB hple hf₁ hf₂
    hd₁ hd₂ hk01 hk02 hk₁ hk₂ hletd₁ hletd₂ hx₁ hx₂ hg₁ hg₂ hconn₁ hconn₂
    (hqside b₁ d₁) (hqside b₂ d₂) (hsside b₁ k₁) (hsside b₂ k₂) hsepn
    (by omega)

end Piece

end HullSC
end GroupApproximation
