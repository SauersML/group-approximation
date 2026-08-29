import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMixedClose

/-!
# The other mixed order

The member carrying the direct powers is the SECOND one, and the case is not the
first one with the letters relabelled.  Two things genuinely change.

**The gap runs the other way.**  `HullSC.false_of_span_mixed` wants the gap
between the two matches bounded by the gap between their sources, which is what
`GGT.OsinComponents.gap_and_order_of_two_matches` returns.
`HullSC.false_of_mixedMatch_gap_inv` wants the SOURCE gap bounded by the gap
between the matches --- the opposite direction --- so that lemma is no use here
and the bound comes from `GGT.OsinComponents.index_le_of_connector_qg` applied
twice instead, once per match, using both of its inequalities rather than one.

**The slack is bigger.**  Bounding a gap by pinning at both ends costs
`eps + 1 + b` twice, so the slack is `2(eps + 1 + b)` --- exactly
`HullSC.blockSeparation` --- where the direct order pays only `b + 2`.  The
length clause therefore has a different constant from clause (C3) as stated for
the direct order: `2(d₂ - d₁) + 3·blockSeparation < |R|` rather than
`2(d₂ - d₁) + (b + 2) < |R|`.  Both are met by taking the run long, but they are
not the same number and the Ledger should say so.

Everything else --- reading the far letter, recovering its component, running
the polygon, the `k - 1` convention of the reversed side --- is as in the direct
order.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section MixedInv

variable {G : Type u} [Group G]

/-- **One matched pair, in the other order.**

The source side carries the inverses and the target side the direct powers, so
the relation comes out as `X · (a_b^f)⁻¹ · X' = a_b^e`, which is the shape
`HullSC.false_of_mixedMatch_gap_inv` reads. -/
theorem mixed_data_of_found_match_inv {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps bn : ℕ} {ms : List ℕ}
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    {p : List G} {c c' d k : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hd : d < u.length) (hk0 : 0 < k) (hk : k ≤ u'.length)
    {b : Bool} {f : ℕ}
    (hletd : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)))
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
    ∃ (e : ℕ) (X X' : G), e ∈ ms ∧
      ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
        = some (GGT.RelLetter.comp b
            ((if b then a true else a false) ^ e)) ∧
      X ∈ D.relBall b eps ∧ X' ∈ D.relBall b eps ∧
      X * (a b ^ f)⁻¹ * X' = a b ^ e := by
  have hkk : k - 1 + 1 = k := by omega
  have hu'len : u'.length
      ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hxR : ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b x) := by
    rw [hw']
    exact (List.getElem?_append_left (by omega : k - 1 < u'.length)).trans hx
  obtain ⟨e, he, hxe⟩ := exponent_of_comp_rotate hxR
  have hletk : ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b
          ((if b then a true else a false) ^ e)) := by
    rw [hxR, hxe]
  have hlu : u[d]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)) := by
    rw [← hletd, hw]
    exact (List.getElem?_append_left hd).symm
  have hlu' : u'[k - 1]?
      = some (GGT.RelLetter.comp b
          ((if b then a true else a false) ^ e)) := by
    rw [hx, hxe]
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw hd hletd
  have hcompu' : GGT.OsinComponents.IsComp b u' (k - 1) (k - 1 + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw' (by omega) hletk
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
  exact ⟨e, _, _, he, hletk, hxb, hx'b, hid⟩

/-- **The other mixed order, closed.**

The gap is bounded by pinning at both ends rather than by the connector-pair
estimate, which is why the slack is `blockSeparation` and not `b + 2`. -/
theorem false_of_mixedMatch_found_inv {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {eps bn : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
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
    {bb : ℝ} {cnt epsPin : ℕ}
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
    {d₁ d₂ k₁ k₂ : ℕ} {b₁ b₂ : Bool} {f₁ f₂ : ℕ}
    (hf₁ : f₁ ∈ ms) (hf₂ : f₂ ∈ ms)
    (hd₁ : d₁ < u.length) (hd₂ : d₂ < u.length)
    (hk01 : 0 < k₁) (hk02 : 0 < k₂)
    (hk₁ : k₁ ≤ u'.length) (hk₂ : k₂ ≤ u'.length)
    (hletd₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[d₁]?
      = some (GGT.RelLetter.comp b₁
          (((if b₁ then a true else a false) ^ f₁)⁻¹)))
    (hletd₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[d₂]?
      = some (GGT.RelLetter.comp b₂
          (((if b₂ then a true else a false) ^ f₂)⁻¹)))
    {x₁ x₂ : G}
    (hx₁ : u'[k₁ - 1]? = some (GGT.RelLetter.comp b₁ x₁))
    (hx₂ : u'[k₂ - 1]? = some (GGT.RelLetter.comp b₂ x₂))
    {h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam b₁) (hh₂ : h₂ ∈ D.fam b₂)
    (hconn₁ : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d₁ * h₁
      = GGT.OsinComponents.vertex (1 : G) u' k₁)
    (hconn₂ : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d₂ * h₂
      = GGT.OsinComponents.vertex (1 : G) u' k₂)
    (hqside₁ : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d₁ →
      (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b₁)
    (hqside₂ : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d₂ →
      (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b₂)
    (hsside₁ : ∀ m : ℕ, m ≤ u'.length → m ≠ k₁ →
      (GGT.OsinComponents.vertex (1 : G) u' k₁)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b₁)
    (hsside₂ : ∀ m : ℕ, m ≤ u'.length → m ≠ k₂ →
      (GGT.OsinComponents.vertex (1 : G) u' k₂)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b₂)
    (hsepn : d₁ + blockSeparation p cnt epsPin < d₂)
    (hlong : 2 * (d₂ - d₁) + 3 * blockSeparation p cnt epsPin
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hsepdef : blockSeparation p cnt epsPin
      = 2 * (epsPin + 1 + blockConst p cnt) := rfl
  have hulen : u.length
      ≤ (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'len : u'.length
      ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hrev : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length
      = (relatorWord₂ p (a false) (a true) ms).length := RelWord.length_revInv _
  obtain ⟨e₁, X₁, X₁', he₁, hl₁, hX₁, hX₁', hid₁⟩ :=
    mixed_data_of_found_match_inv hpair hp0 hw hw' hd₁ hk01 hk₁ hletd₁ hx₁ hh₁
      hconn₁ hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside₁ hsside₁
  obtain ⟨e₂, X₂, X₂', he₂, hl₂, hX₂, hX₂', hid₂⟩ :=
    mixed_data_of_found_match_inv hpair hp0 hw hw' hd₂ hk02 hk₂ hletd₂ hx₂ hh₂
      hconn₂ hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside₂ hsside₂
  obtain ⟨hp₁, hp₁'⟩ :=
    GGT.OsinComponents.index_le_of_connector_qg D hqlet hslet hqgq hqgs hB
      (by omega : d₁ ≤ u.length) hk₁ hple hh₁ hconn₁
  obtain ⟨hp₂, hp₂'⟩ :=
    GGT.OsinComponents.index_le_of_connector_qg D hqlet hslet hqgq hqgs hB
      (by omega : d₂ ≤ u.length) hk₂ hple hh₂ hconn₂
  exact false_of_mixedMatch_gap_inv
    (gapSlack := blockSeparation p cnt epsPin) hnodup hinj hsymm hsep
    (by omega) (by omega) (by omega) (by omega) he₁ hf₁ he₂ hf₂ hX₁ hX₁' hX₂
    hX₂' hid₁ hid₂ hl₁ hletd₁ hl₂ hletd₂ (by omega) (by omega)

end MixedInv

end HullSC
end GroupApproximation
