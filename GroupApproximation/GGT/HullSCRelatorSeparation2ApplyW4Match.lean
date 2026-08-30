import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMatch
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyTwoBlock
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyW4Adjacent

/-!
# A match whose second gap is trivial

The aligned cases used to force their connectors trivial with a design clause
about commutation, which `GGT/HullSCRelatorSeparation2ApplyLoxGap.lean` shows
cannot be discharged at this core.  Hull does not need one: his pieces exclude
the conjugacy identity syntactically, and what makes the connector trivial is
(W4), that the two subgroups meet only in the identity.

This module is the step that spends it.  It replaces the finder AND the
matching step inside the piece theorems --- it returns the component it settled
on, the match at it, and the equation the closers now take.

## The shape of the argument

Three consecutive block letters, at `d`, `d + 1`, `d + 2`; run the matching
step at each.  For a pair of adjacent components the second gap of the first
match and the first gap of the second are INVERSE, because they share the
near-side vertex, so that element lies in both subgroups and (W4) kills it ---
`HullSC.trivialGap_of_two_connectors`, which reads the two connectors the
matching step returns rather than the polygon's gaps.

Two things have to be checked before that applies.  The far-side components
must be adjacent, `k₁ = k₀ + 1`, which is
`HullSC.farSide_adjacent_of_matches`, resting on the unique occurrence of each
exponent; and the two indices must be opposite, which is
`HullSC.index_alternates_of_rotate`.

## Why three letters and not two

`farSide_adjacent_of_matches` needs `k₀ < |R|`, and that fails exactly when the
far component of the first match is the last letter of a piece that is the
whole rotation.  With three letters there are two candidate pairs, and their
far components carry opposite indices, so they are distinct and at most one can
be last.  The alternation does that work; no exponent argument is needed for
it.

## Where `hpair` survives

Only for the two exponent equalities.  The matching step returns a connector
but no bound on it, and `HullSC.exponent_eq_of_blockMatch_ball` --- which is
what pins a far-side letter to the same letter of the relator as its near-side
one --- wants both connectors in the relative ball.  That is the polygon's
output and nothing else in the argument uses it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section W4Match

variable {G : Type u} [Group G] {D : GGT.RelGenSet G Bool} {a : Bool → G}
  {eps rho Cm bn : ℕ} {ms : List ℕ}

/-- **The far-side letter of a match sits at the same letter of the relator.**

The matching step returns a connector but no bound on it, so the pinning goes
through the polygon: `hpair` puts both gaps of the matched pair in the relative
ball, `HullSC.conj_of_matchedPair_letters` turns them into the connector
relation, and `HullSC.exponent_eq_of_blockMatch_ball` reads the exponents off
it.  This is the only place the (W4) argument spends the polygon. -/
theorem exponent_eq_of_pieceMatch
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
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
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam t)
    {n k : ℕ} {b : Bool} {e : ℕ} {x h : G} (he : e ∈ ms)
    (hn : n < u.length) (hk0 : 0 < k) (hk : k ≤ u'.length)
    (hln : ((relatorWord₂ p (a false) (a true) ms).rotate c)[n]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hx : u'[k - 1]? = some (GGT.RelLetter.comp b x))
    (hh : h ∈ D.fam b)
    (hc : GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u n * h
      = GGT.OsinComponents.vertex (1 : G) u' k) :
    ∃ f : ℕ, f ∈ ms ∧ e = f ∧
      ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
        = some (GGT.RelLetter.comp b
            ((if b then a true else a false) ^ f)) := by
  have hu'len : u'.length
      ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hxR : ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b x) := by
    rw [hw']
    exact (List.getElem?_append_left (by omega : k - 1 < u'.length)).trans hx
  obtain ⟨f, hf, hxf⟩ := exponent_of_comp_rotate hxR
  have hletk : ((relatorWord₂ p (a false) (a true) ms).rotate c')[k - 1]?
      = some (GGT.RelLetter.comp b
          ((if b then a true else a false) ^ f)) := by
    rw [hxR, hxf]
  have hkk : k - 1 + 1 = k := by omega
  have hcompu : GGT.OsinComponents.IsComp b u n (n + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hn hln
  have hcompu' : GGT.OsinComponents.IsComp b u' (k - 1) (k - 1 + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw' (by omega) hletk
  have hc' : GGT.RelLetter.listVal py *
      GGT.OsinComponents.vertex (1 : G) u n * h
      = GGT.OsinComponents.vertex (1 : G) u' (k - 1 + 1) := by
    rw [hkk]
    exact hc
  have hConn := GGT.OsinComponents.connected_of_connector D b py u pz u'
    hclose (by omega : n ≤ u.length) (k - 1 + 1) hh hc'
  have hsside' : ∀ m : ℕ, m ≤ u'.length → m ≠ k - 1 + 1 →
      GGT.OsinComponents.IsCompStart b
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' (k - 1 + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b := by
    rw [hkk]
    exact hsside b k
  obtain ⟨hxb, hx'b⟩ := hpair b py u pz u' n (k - 1) hclose hlet4 hpy hpz hpy0
    hqg hcompu (Or.inr hpz0) hcompu' (Or.inr hpz0) hConn (hqside b n) hsside'
  have hlu : u[n]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ e)) := by
    rw [← hln, hw]
    exact (List.getElem?_append_left hn).symm
  have hxu' : u'[k - 1]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ f)) := by
    rw [hx, hxf]
  have hrel := conj_of_matchedPair_letters (py := py) hlu hxu'
  rw [ite_apply_eq a b] at hrel
  exact ⟨f, hf, exponent_eq_of_blockMatch_ball hsep he hf hxb hx'b hrel,
    hletk⟩

/-- **A block letter of the piece whose match has a trivial second gap.**

This replaces the finder and the matching step together, and returns the
component it settled on.  Three consecutive block letters; the matching step at
each; then the pair whose far-side component is not the last letter of `u'`.
For that pair the second gap of the first match is the inverse of the first gap
of the second, so it lies in both subgroups, and (W4) makes it `1`. -/
theorem exists_match_with_trivialGap
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hrho : Cm * 4 ≤ rho) (hms : 5 ≤ ms.length)
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    (hmatch : GGT.OsinComponents.DeepMatchOutput D Cm bn)
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
    ∃ (d : ℕ) (b : Bool) (e k : ℕ), d < u.length ∧ e ∈ ms ∧
      ((relatorWord₂ p (a false) (a true) ms).rotate c)[d]?
        = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)) ∧
      0 < k ∧ k ≤ u'.length ∧
      (∃ x : G, u'[k - 1]? = some (GGT.RelLetter.comp b x)) ∧
      (∃ h : G, h ∈ D.fam b ∧
        GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u d * h
          = GGT.OsinComponents.vertex (1 : G) u' k) ∧
      (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (d + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' k = 1 := by
  have hulen : u.length ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'len : u'.length ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  have hpolyq := GGT.OsinComponents.isQuasiGeodesicPolygon_fourGon py u pz u' D
    hlet4 hclose hqg
  have hstep : ∀ (n : ℕ) (bb : Bool) (ee : ℕ), ee ∈ ms → n < u.length →
      ((relatorWord₂ p (a false) (a true) ms).rotate c)[n]?
        = some (GGT.RelLetter.comp bb
            ((if bb then a true else a false) ^ ee)) →
      ∃ k : ℕ, 0 < k ∧ k ≤ u'.length ∧
        (∃ x : G, u'[k - 1]? = some (GGT.RelLetter.comp bb x)) ∧
        ∃ h : G, h ∈ D.fam bb ∧
          GGT.RelLetter.listVal py *
              GGT.OsinComponents.vertex (1 : G) u n * h
            = GGT.OsinComponents.vertex (1 : G) u' k := by
    intro n bb ee hee hn hln
    have hlu : u[n]? = some (GGT.RelLetter.comp bb
        ((if bb then a true else a false) ^ ee)) := by
      rw [← hln, hw]
      exact (List.getElem?_append_left hn).symm
    have hspan : (GGT.OsinComponents.vertex (1 : G) u n)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u (n + 1) = a bb ^ ee := by
      rw [span_eq_val_of_getElem? hlu]
      show (if bb then a true else a false) ^ ee = a bb ^ ee
      rw [ite_apply_eq a bb]
    have hdeepspan : (GGT.OsinComponents.vertex (1 : G) u n)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u (n + 1) ∉ D.relBall bb rho := by
      rw [hspan]
      exact (hdeep ee hee bb).1
    have hcompu : GGT.OsinComponents.IsComp bb u n (n + 1) :=
      isComp_prefix_rotate_relatorWord₂ hp0 hw hn hln
    exact hmatch bb rho py u pz u' n hrho hclose hpy hpz hpz0 hpolyq hcompu
      hdeepspan (hqside bb n)
  have hvalu : ∀ (n : ℕ) (bb : Bool) (ee : ℕ), n < u.length →
      ((relatorWord₂ p (a false) (a true) ms).rotate c)[n]?
        = some (GGT.RelLetter.comp bb
            ((if bb then a true else a false) ^ ee)) →
      (GGT.OsinComponents.vertex (1 : G) u n)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u (n + 1) ∈ D.fam bb := by
    intro n bb ee hn hln
    have hlu : u[n]? = some (GGT.RelLetter.comp bb
        ((if bb then a true else a false) ^ ee)) := by
      rw [← hln, hw]
      exact (List.getElem?_append_left hn).symm
    have hmem : GGT.RelLetter.comp bb
        ((if bb then a true else a false) ^ ee) ∈ u := List.mem_of_getElem? hlu
    have hlet : D.IsLetter (GGT.RelLetter.comp bb
        ((if bb then a true else a false) ^ ee)) :=
      hlet4 _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hmem)))
    rw [span_eq_val_of_getElem? hlu]
    exact hlet
  obtain ⟨d, b₀, b₁, b₂, e₀, e₁, e₂, hd2, he₀, he₁, he₂, hl₀, hl₁,
      hl₂⟩ :=
    exists_three_blocks_of_long_prefix_rotate (h₀ := a false) (h₁ := a true)
      (c := c) hms hlong
  have hl₂' : ((relatorWord₂ p (a false) (a true) ms).rotate c)[d + 1 + 1]?
      = some (GGT.RelLetter.comp b₂
          ((if b₂ then a true else a false) ^ e₂)) := hl₂
  obtain ⟨k₀, hk₀0, hk₀, ⟨x₀, hx₀⟩, h₀, hh₀, hc₀⟩ :=
    hstep d b₀ e₀ he₀ (by omega) hl₀
  obtain ⟨k₁, hk₁0, hk₁, ⟨x₁, hx₁⟩, h₁, hh₁, hc₁⟩ :=
    hstep (d + 1) b₁ e₁ he₁ (by omega) hl₁
  obtain ⟨k₂, hk₂0, hk₂, ⟨x₂, hx₂⟩, h₂, hh₂, hc₂⟩ :=
    hstep (d + 2) b₂ e₂ he₂ (by omega) hl₂
  have halt₀ : b₁ = !b₀ :=
    index_alternates_of_rotate hp0 (by omega) (by omega) hl₀ hl₁
  have halt₁ : b₂ = !b₁ :=
    index_alternates_of_rotate hp0 (by omega) (by omega) hl₁ hl₂'
  have hne : k₀ ≠ k₁ := by
    intro hk
    have hx₁' : u'[k₀ - 1]? = some (GGT.RelLetter.comp b₁ x₁) := by
      rw [hk]
      exact hx₁
    rw [hx₀] at hx₁'
    have hb : b₀ = b₁ := by
      have hinj₂ := Option.some.inj hx₁'
      rw [GGT.RelLetter.comp.injEq] at hinj₂
      exact hinj₂.1
    rw [halt₀] at hb
    revert hb
    cases b₀ with
    | false => simp
    | true => simp
  rcases Nat.lt_or_ge k₀
      (relatorWord₂ p (a false) (a true) ms).length with hlt₀ | hge₀
  · obtain ⟨f₀, hf₀, hef₀, hlk₀⟩ := exponent_eq_of_pieceMatch hsep hpair hp0
      hw hw' hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside hsside he₀ (by omega)
      hk₀0 hk₀ hl₀ hx₀ hh₀ hc₀
    obtain ⟨f₁, hf₁, hef₁, hlk₁⟩ := exponent_eq_of_pieceMatch hsep hpair hp0
      hw hw' hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside hsside he₁ (by omega)
      hk₁0 hk₁ hl₁ hx₁ hh₁ hc₁
    rw [← hef₀] at hlk₀
    rw [← hef₁] at hlk₁
    have hadj : k₁ = k₀ + 1 :=
      farSide_adjacent_of_matches hinj' hnodup (by omega) (by omega) (by omega)
        (by omega) hk₀0 hk₁0 hlt₀ hl₀ hl₁ hlk₀ hlk₁
    have hx₁' : u'[k₀]? = some (GGT.RelLetter.comp b₁ x₁) := by
      rw [hadj, Nat.add_sub_cancel] at hx₁
      exact hx₁
    have hvk : (GGT.OsinComponents.vertex (1 : G) u' k₀)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' k₁ = x₁ := by
      rw [hadj]
      exact span_eq_val_of_getElem? hx₁'
    have hvkm : x₁ ∈ D.fam b₁ := hslet _ (List.mem_of_getElem? hx₁')
    have hgap := trivialGap_of_two_connectors hdisj halt₀ hh₀ hh₁ hc₀ hc₁ rfl
      (hvalu d b₀ e₀ (by omega) hl₀) hvk hvkm
    exact ⟨d, b₀, e₀, k₀, by omega, he₀, hl₀, hk₀0, hk₀, ⟨x₀, hx₀⟩,
      ⟨h₀, hh₀, hc₀⟩, hgap⟩
  · have hlt₁ : k₁ < (relatorWord₂ p (a false) (a true) ms).length := by
      omega
    obtain ⟨f₁, hf₁, hef₁, hlk₁⟩ := exponent_eq_of_pieceMatch hsep hpair hp0
      hw hw' hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside hsside he₁ (by omega)
      hk₁0 hk₁ hl₁ hx₁ hh₁ hc₁
    obtain ⟨f₂, hf₂, hef₂, hlk₂⟩ := exponent_eq_of_pieceMatch hsep hpair hp0
      hw hw' hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside hsside he₂ (by omega)
      hk₂0 hk₂ hl₂ hx₂ hh₂ hc₂
    rw [← hef₁] at hlk₁
    rw [← hef₂] at hlk₂
    have hadj : k₂ = k₁ + 1 :=
      farSide_adjacent_of_matches hinj' hnodup (by omega) (by omega) (by omega)
        (by omega) hk₁0 hk₂0 hlt₁ hl₁ hl₂' hlk₁ hlk₂
    have hx₂' : u'[k₁]? = some (GGT.RelLetter.comp b₂ x₂) := by
      rw [hadj, Nat.add_sub_cancel] at hx₂
      exact hx₂
    have hvk : (GGT.OsinComponents.vertex (1 : G) u' k₁)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' k₂ = x₂ := by
      rw [hadj]
      exact span_eq_val_of_getElem? hx₂'
    have hvkm : x₂ ∈ D.fam b₂ := hslet _ (List.mem_of_getElem? hx₂')
    have hgap := trivialGap_of_two_connectors hdisj halt₁ hh₁ hh₂ hc₁ hc₂ rfl
      (hvalu (d + 1) b₁ e₁ (by omega) hl₁) hvk hvkm
    exact ⟨d + 1, b₁, e₁, k₁, by omega, he₁, hl₁, hk₁0, hk₁, ⟨x₁, hx₁⟩,
      ⟨h₁, hh₁, hc₁⟩, hgap⟩

end W4Match

end HullSC
end GroupApproximation
