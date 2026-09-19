import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyPiece
import GroupApproximation.GGT.HullSCRelatorSeparation2Assemble

/-!
# The four cases, instantiated at one quadrilateral

`HullSC.listVal_conj_of_sym_cases` takes the four cases of a match between two
members of the symmetrized closure as obligations; the four piece-level
theorems of `GGT/HullSCRelatorSeparation2ApplyPiece.lean` discharge them.  This
module puts the two together, and that is all it does: the mathematics is
above it and below it, and what is between is the observation that the
quadrilateral is the same in all four cases.

The two long sides are the two pieces, so the polygon's data --- the letters,
the closing identity, the quasi-geodesic clause, the two same-side exclusions
--- does not depend on which of the four cases holds, and neither do the
design's clauses.  Only the two spellings change, and they change together
with the case.

**What the caller still owes.**  Three things, and the Ledger lists them under
the same names.

* `hqg`, the four-gon's quasi-geodesic clause, which is where the cyclic
  quasi-geodesicity of the relator enters;
* `hqside` and `hsside`, the two same-side exclusions;
* the two spellings `py`, `pz` of the separation's `y` and `z`, with
  `0 < py.length` and `0 < pz.length`.

**What the caller must take.**  `u`, the piece, longer than
`|p| + blockSeparation + 1` --- so `B := |p| + blockSeparation + 2` --- and the
exponent list longer than `|p| + 5 * blockSeparation + 2`.  Both are
hypotheses here in exactly the shape the construction produces them.

The two aligned cases ask for less than that and are discharged from the same
two numbers: they want a window of `|p| + 5` and five exponents, and
`blockSeparation = 2(eps + 1 + b)` is at least `4` once `p` is non-empty.
Neither constant has to grow.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section FourWay

variable {G : Type u} [Group G] {D : GGT.RelGenSet G Bool} {a : Bool → G}
  {eps rho Cm bn : ℕ} {ms : List ℕ}

variable
  (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
  (hmatch : GGT.OsinComponents.DeepMatchOutput D Cm bn)

include hpair hmatch in
/-- **The separation's conclusion at one quadrilateral.**

Two members of the symmetrized closure with matched long prefixes, and the
conjugation Olshanskii's step (a) asks for, by the four cases: the two aligned
ones close and the two mixed ones are excluded. -/
theorem listVal_conj_of_sym_pieces (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho)
    {p : List G} (hp0 : 0 < p.length) {bb : ℝ} {cnt epsPin : ℕ}
    {py pz u u' w w' tl tl' : List (GGT.RelLetter G Bool)}
    (hwsym : RelWord.Sym (relatorWord₂ p (a false) (a true) ms) w)
    (hwsym' : RelWord.Sym (relatorWord₂ p (a false) (a true) ms) w')
    (hu : w = u ++ tl) (hu' : w' = u' ++ tl')
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
    (hqside : ∀ (t : Bool) (d i' : ℕ),
      GGT.OsinComponents.IsComp t u d (d + 1) →
      i' ≤ u.length → i' ≠ d →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam t)
    (hsside : ∀ (t : Bool) (k m : ℕ),
      (∃ j : ℕ, j + 1 = k ∧ GGT.OsinComponents.IsComp t u' j k) →
      m ≤ u'.length → m ≠ k →
      GGT.OsinComponents.IsCompStart t
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t) :
    GGT.RelLetter.listVal w'
      = GGT.RelLetter.listVal py * GGT.RelLetter.listVal w *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hbs : 4 ≤ blockSeparation p cnt epsPin := by
    have hval : blockSeparation p cnt epsPin
        = 2 * (epsPin + 1 + (p.length + cnt)) := rfl
    omega
  have hms : 5 ≤ ms.length := by omega
  have hlong : p.length + 4 < u.length := by omega
  refine listVal_conj_of_sym_cases hwsym hwsym' ?_ ?_ ?_ ?_
  · intro c c' hc hc'
    subst hc
    subst hc'
    exact listVal_conj_of_alignedMatch_piece hpair hmatch hnodup hinj hsep
      hdisj hdeep hrho hms hp0 hu hu' hlong hpy hpz hpy0 hpz0 hlet4 hslet
      hclose hqg hqside hsside
  · intro c c' hc hc'
    subst hc
    subst hc'
    exact listVal_conj_of_mirroredAlignedMatch_piece hpair hmatch hnodup hinj
      hsymm hsep hdisj hdeep hrho hms hp0 hu hu' hlong hpy hpz hpy0 hpz0 hlet4
      hslet hclose hqg hqside hsside
  · intro c c' hc hc'
    subst hc
    subst hc'
    exact false_of_mixedMatch_piece hpair hmatch hnodup hinj hsep hdeep hrho
      hp0 hu hu' hlongp hmslong hpy hpz hpy0 hpz0 hlet4 hclose hqg hqlet hslet
      hqgq hqgs hB hple hqside hsside
  · intro c c' hc hc'
    subst hc
    subst hc'
    exact false_of_mixedMatch_piece_inv hpair hmatch hnodup hinj hsymm hsep
      hdeep hrho hp0 hu hu' hlongp hmslong hpy hpz hpy0 hpz0 hlet4 hclose hqg
      hqlet hslet hqgq hqgs hB hple hqside hsside

end FourWay

end HullSC
end GroupApproximation
