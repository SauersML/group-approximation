import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMatch

/-!
# The mixed case, from two found matches

The aligned branches spend the polygon's gaps BY NAME, because the join reads
the vertex relation.  The mixed branches do not: they read the connector
relation only, so the gaps can stay behind an existential, and what they need
instead is a second match and an ORDER between the two.

`mixed_data_of_found_match` is the per-match half.  It reads the far letter into
the design's shape, recovers its component, runs the polygon, and returns what
`HullSC.false_of_span_mixed` asks of one matched pair: the exponent, the two
gaps in the ball, and the relation `X · a_b^e · X' = (a_b^f)⁻¹`.  The index
convention of the reversed side is spent here as it is in the aligned case ---
the match returns at `k`, the far component is `[k - 1, k)`.

`false_of_mixedMatch_found` is the composition: the per-match half twice, the
order and the gap from
`GGT.OsinComponents.gap_and_order_of_two_matches`, and the estimate closes it.
The separation hypothesis is where clause (C2) of the construction is spent, and
it is spent against `eps + 1 + Bn`, NOT `eps + 1`: the geodesic pinning is not
available for these sides.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Mixed

variable {G : Type u} [Group G]

/-- **One matched pair, in the shape the mixed estimate consumes.** -/
theorem mixed_data_of_found_match {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps bn : ℕ} {ms : List ℕ}
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    {p : List G} {c c' d k : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    (hd : d < u.length) (hk0 : 0 < k) (hk : k ≤ u'.length)
    {b : Bool} {e : ℕ}
    (hletd : ((relatorWord₂ p (a false) (a true) ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    {x : G} (hx : u'[k - 1]? = some (GGT.RelLetter.comp b x))
    {h : G} (hh : h ∈ D.fam b)
    (hconn : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' k)
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
    (hqside : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b)
    (hsside : ∀ m : ℕ, m ≤ u'.length → m ≠ k →
      (GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b) :
    ∃ (f : ℕ) (X X' : G), f ∈ ms ∧
      ((RelWord.revInv
          (relatorWord₂ p (a false) (a true) ms)).rotate c')[k - 1]?
        = some (GGT.RelLetter.comp b
            (((if b then a true else a false) ^ f)⁻¹)) ∧
      X ∈ D.relBall b eps ∧ X' ∈ D.relBall b eps ∧
      X * a b ^ e * X' = (a b ^ f)⁻¹ := by
  have hkk : k - 1 + 1 = k := by omega
  have hu'len : u'.length
      ≤ (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hxR : ((RelWord.revInv
      (relatorWord₂ p (a false) (a true) ms)).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b x) := by
    rw [hw']
    exact (List.getElem?_append_left (by omega : k - 1 < u'.length)).trans hx
  obtain ⟨f, hf, hxf⟩ := exponent_of_comp_rotate_revInv hxR
  have hletk : ((RelWord.revInv
      (relatorWord₂ p (a false) (a true) ms)).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)) := by
    rw [hxR, hxf]
  have hlu : u[d]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)) := by
    rw [← hletd, hw]
    exact (List.getElem?_append_left hd).symm
  have hlu' : u'[k - 1]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)) := by
    rw [hx, hxf]
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hd hletd
  have hcompu' : GGT.OsinComponents.IsComp b u' (k - 1) (k - 1 + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw' (by omega) hletk
  have hconn' : GGT.RelLetter.listVal py *
      GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' (k - 1 + 1) := by
    rw [hkk]
    exact hconn
  have hsside' : ∀ m : ℕ, m ≤ u'.length → m ≠ k - 1 + 1 →
      (GGT.OsinComponents.vertex (1 : G) u' (k - 1 + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b := by
    rw [hkk]
    exact hsside
  have hConn := GGT.OsinComponents.connected_of_connector D b py u pz u' hclose
    (by omega : d ≤ u.length) (k - 1 + 1) hh hconn'
  obtain ⟨hxb, hx'b⟩ := hpair b py u pz u' d (k - 1) hclose hlet4 hpy hpz hpy0
    hqg hcompu (Or.inr hpz0) hcompu' (Or.inr hpz0) hConn hqside hsside'
  have hid := conj_of_matchedPair_letters (py := py) hlu hlu'
  rw [ite_apply_eq a b] at hid
  exact ⟨f, _, _, hf, hletk, hxb, hx'b, hid⟩

end Mixed

end HullSC
end GroupApproximation
