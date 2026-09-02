import GroupApproximation.GGT.HullSCRelatorSeparation2AdjacentGap
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyW4Adjacent
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyClose

/-!
# Closing exact published matches with relative short sides

Hull's Proposition 5.3 measures the two short sides in the full relative
alphabet.  The published-gap outputs already return the bounded gaps and the
connectors without asking those sides to consist of base letters.  This module
uses that output directly.

For aligned orientations, two adjacent clean matches have adjacent images.
The seam certificate on the second image rules out the only wrap case, and
(W4) makes the shared gap trivial.  The existing aligned closers then give the
full conjugacy identity.

For opposite orientations, the same exponent occurs at reflected positions.
Thus the two far components occur in reverse adjacent order.  The middle
connector is a conjugate, inside one peripheral subgroup, of the first
connector, while it belongs to the other peripheral subgroup by construction.
(W4) makes it trivial, so one bounded polygon gap is an entire positive or
negative design power, contradicting the depth clause.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Arithmetic

/-- At a singleton base word, the raised strict prefix threshold has exactly
the capacity required for two relative spellings of maximal length `eps + 2`.
The left side is the first admissible natural length above the threshold. -/
theorem exactPublishedAdjacentCapacity_singleton (g : G) (eps : ℕ) :
    [g].length + blockSeparation [g] (max 1 (eps + 2)) eps + 6 + 1 =
      2 * ((eps + 2) + (eps + 2) + 3) + 2 := by
  simp only [blockSeparation, blockConst, List.length_singleton]
  omega

/-- Two aligned adjacent matches cannot put the first far component at the
last endpoint when the second endpoint is seam-clean. -/
theorem farEnd_lt_of_aligned_seam {L c c' i j j' : ℕ}
    (_hL : 0 < L) (hj1 : 1 < j) (hj : j ≤ L) (hj'1 : 1 < j') (hj' : j' ≤ L)
    (h₀ : (c + i) % L = (c' + (j - 1)) % L)
    (h₁ : (c + (i + 1)) % L = (c' + (j' - 1)) % L) :
    j < L := by
  by_contra hnot
  have hjL : j = L := by omega
  have hstep : (c + (i + 1)) % L = (c' + j) % L := by
    rw [show c + (i + 1) = c + i + 1 from by omega,
      show c' + j = c' + (j - 1) + 1 from by omega,
      Nat.add_mod (c + i) 1 L, Nat.add_mod (c' + (j - 1)) 1 L, h₀]
  have hmod : j % L = (j' - 1) % L := by
    apply Nat.ModEq.add_left_cancel' c'
    show (c' + j) % L = (c' + (j' - 1)) % L
    rw [← hstep, h₁]
  rw [hjL, Nat.mod_self, Nat.mod_eq_of_lt (by omega : j' - 1 < L)] at hmod
  omega

/-- Reflected adjacent matches occur in reverse adjacent order.  The two
position-sum identities are the position statement of the two pinned
exponents; seam-clean endpoints turn their modular relation into equality. -/
theorem farEnd_pred_of_mirrored_seam {L c c' i j j' : ℕ}
    (_hL : 0 < L) (hj1 : 1 < j) (hj : j ≤ L) (hj'1 : 1 < j') (hj' : j' ≤ L)
    (h₀ : (c + i) % L + (c' + (j - 1)) % L = L - 1)
    (h₁ : (c + (i + 1)) % L + (c' + (j' - 1)) % L = L - 1) :
    j = j' + 1 := by
  have hs₀ : (c + i + (c' + (j - 1))) % L = (L - 1) % L := by
    rw [Nat.add_mod, h₀]
  have hs₁ : (c + (i + 1) + (c' + (j' - 1))) % L = (L - 1) % L := by
    rw [Nat.add_mod, h₁]
  have hsum : c + c' + (i + (j - 1)) ≡
      c + c' + ((i + 1) + (j' - 1)) [MOD L] := by
    show (c + c' + (i + (j - 1))) % L =
      (c + c' + ((i + 1) + (j' - 1))) % L
    rw [show c + c' + (i + (j - 1)) = c + i + (c' + (j - 1)) from by omega,
      show c + c' + ((i + 1) + (j' - 1)) =
        c + (i + 1) + (c' + (j' - 1)) from by omega,
      hs₀, hs₁]
  have hsum' : i + (j - 1) ≡ (i + 1) + (j' - 1) [MOD L] :=
    Nat.ModEq.add_left_cancel' (c + c') hsum
  have htail : j - 1 ≡ j' [MOD L] := by
    apply Nat.ModEq.add_left_cancel' i
    convert hsum' using 1
    all_goals omega
  have hmod : (j - 1) % L = j' % L := htail
  have hj'lt : j' < L := by
    by_contra hnot
    have hj'L : j' = L := by omega
    rw [hj'L, Nat.mod_self,
      Nat.mod_eq_of_lt (by omega : j - 1 < L)] at hmod
    omega
  rw [Nat.mod_eq_of_lt (by omega : j - 1 < L),
    Nat.mod_eq_of_lt hj'lt] at hmod
  omega

end Arithmetic

section Connector

variable {G : Type u} [Group G]

/-- The preceding connector calculation in the form used by W4.  Membership
of the source component span supplies the conjugating element. -/
theorem reverseAdjacent_connector_eq_one {D : GGT.RelGenSet G Bool}
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {b b' : Bool} (halt : b' = !b) {Y A B V W h h' g : G}
    (hg : g ∈ D.fam b) (hh : h ∈ D.fam b) (hh' : h' ∈ D.fam b')
    (hAB : A⁻¹ * B = g) (hVW : V⁻¹ * W = g⁻¹)
    (hc : Y * A * h = W) (hc' : Y * B * h' = V) :
    h' = 1 := by
  have hhEq : (Y * A)⁻¹ * W = h := by
    rw [← hc]
    group
  have hh'Eq : (Y * B)⁻¹ * V = h' := by
    rw [← hc']
    group
  have hB : B = A * g := by
    calc
      B = A * (A⁻¹ * B) := by group
      _ = A * g := by rw [hAB]
  have hW : W = V * g⁻¹ := by
    calc
      W = V * (V⁻¹ * W) := by group
      _ = V * g⁻¹ := by rw [hVW]
  have heq : h' = g⁻¹ * h * g := by
    rw [← hh'Eq, ← hhEq, hB, hW]
    group
  have hb : h' ∈ D.fam b := by
    rw [heq]
    exact mul_mem (mul_mem (inv_mem hg) hh) hg
  exact eq_one_of_mem_both hdisj hb (by simpa only [halt] using hh')

/-- Once the middle connector is trivial, the second gap of the first match is
the entire reverse-oriented far component. -/
theorem secondGap_eq_of_reverseAdjacent {Y B V W h' g : G}
    (hc' : Y * B * h' = V) (hh' : h' = 1) (hVW : V⁻¹ * W = g⁻¹) :
    (Y * B)⁻¹ * W = g⁻¹ := by
  rw [hh', mul_one] at hc'
  rw [hc']
  exact hVW

end Connector

section Aligned

variable {G : Type u} [Group G]

/-- The direct aligned branch from two adjacent published-gap matches.  Every
hypothesis is data returned by `ExactPublishedAdjacentGapOutput` or by the
exact design; no spelling restriction is imposed on either short side. -/
theorem listVal_conj_of_relativeAdjacent_direct
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ} {ms : List ℕ}
    (hnodup : ms.Nodup)
    (hinj : ∀ b : Bool, Function.Injective (fun n : ℕ ↦ a b ^ n))
    (hsep : ∀ e ∈ ms, ∀ f ∈ ms, e ≠ f → ∀ b : Bool,
      ∀ x ∈ D.relBall b eps, ∀ x' ∈ D.relBall b eps,
        x * a b ^ e * x' ≠ a b ^ f ∧ x * a b ^ e * x' ≠ (a b ^ f)⁻¹)
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {p : List G} (hp0 : 0 < p.length) {c c' i j j' : ℕ}
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hi0 : 0 < i) (hi2 : i + 2 < u.length)
    {b b' : Bool}
    (hcomp : GGT.OsinComponents.IsComp b u i (i + 1))
    (hcomp' : GGT.OsinComponents.IsComp b' u (i + 1) (i + 2))
    (hj1 : 1 < j) (hj : j ≤ u'.length)
    (hcompS : GGT.OsinComponents.IsComp b u' (j - 1) j)
    (hj'1 : 1 < j') (hj' : j' ≤ u'.length)
    (hcompS' : GGT.OsinComponents.IsComp b' u' (j' - 1) j')
    {h h' : G} (hh : h ∈ D.fam b) (hh' : h' ∈ D.fam b')
    (hc : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u i * h =
      GGT.OsinComponents.vertex (1 : G) u' j)
    (hc' : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1) * h' =
      GGT.OsinComponents.vertex (1 : G) u' j')
    (hx : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
          ∈ D.relBall b eps)
    (hx' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j ∈ D.relBall b eps)
    (hy : (GGT.OsinComponents.vertex (1 : G) u' (j' - 1))⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1)) ∈ D.relBall b' eps)
    (hy' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 2))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j' ∈ D.relBall b' eps)
    (hqlet : ∀ x ∈ u, D.IsLetter x) (hslet : ∀ x ∈ u', D.IsLetter x) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c') =
      GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c) *
          (GGT.RelLetter.listVal py)⁻¹ := by
  let R := relatorWord₂ p (a false) (a true) ms
  have huLen : u.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'Len : u'.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hqOf := hcomp.2.2.1 i le_rfl (by omega) (by omega)
  obtain ⟨vq, hqi⟩ := getElem?_comp_of_isCompOf (by omega) hqOf
  have hqOf' := hcomp'.2.2.1 (i + 1) le_rfl (by omega) (by omega)
  obtain ⟨vq', hqi'⟩ := getElem?_comp_of_isCompOf (by omega) hqOf'
  have hsOf := hcompS.2.2.1 (j - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs, hsj⟩ := getElem?_comp_of_isCompOf (by omega) hsOf
  have hsOf' := hcompS'.2.2.1 (j' - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs', hsj'⟩ := getElem?_comp_of_isCompOf (by omega) hsOf'
  have hqiR : (R.rotate c)[i]? = some (GGT.RelLetter.comp b vq) := by
    rw [hw, List.getElem?_append_left (by omega : i < u.length)]
    exact hqi
  have hqiR' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b' vq') := by
    rw [hw, List.getElem?_append_left (by omega : i + 1 < u.length)]
    exact hqi'
  have hsjR : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b vs) := by
    rw [hw', List.getElem?_append_left (by omega : j - 1 < u'.length)]
    exact hsj
  have hsjR' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b' vs') := by
    rw [hw', List.getElem?_append_left (by omega : j' - 1 < u'.length)]
    exact hsj'
  obtain ⟨e, he, hvq⟩ := exponent_of_comp_rotate hqiR
  obtain ⟨e', he', hvq'⟩ := exponent_of_comp_rotate hqiR'
  obtain ⟨f, hf, hvs⟩ := exponent_of_comp_rotate hsjR
  obtain ⟨f', hf', hvs'⟩ := exponent_of_comp_rotate hsjR'
  have hqiPow : (R.rotate c)[i]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ e)) := by
    simpa only [hvq] using hqiR
  have hqiPow' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b'
      ((if b' then a true else a false) ^ e')) := by
    simpa only [hvq'] using hqiR'
  have hsjPow : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ f)) := by
    simpa only [hvs] using hsjR
  have hsjPow' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b'
      ((if b' then a true else a false) ^ f')) := by
    simpa only [hvs'] using hsjR'
  have hrel := conj_of_matchedPair_letters (py := py) hqi hsj
  have hrel' := conj_of_matchedPair_letters (py := py) hqi' hsj'
  rw [hvq, hvs, ite_apply_eq a b] at hrel
  rw [hvq', hvs', ite_apply_eq a b'] at hrel'
  have hjstep : j - 1 + 1 = j := by omega
  have hj'step : j' - 1 + 1 = j' := by omega
  rw [hjstep] at hrel
  rw [hj'step] at hrel'
  have hef : e = f := exponent_eq_of_blockMatch_ball hsep he hf hx hx' hrel
  have hef' : e' = f' := exponent_eq_of_blockMatch_ball hsep he' hf' hy hy' hrel'
  have hinj' : ∀ t : Bool, Function.Injective
      (fun n : ℕ ↦ (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  have hpos := position_eq_of_alignedMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
    hef (by simpa only [R] using hqiPow) (by simpa only [R] using hsjPow)
  have hpos' := position_eq_of_alignedMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
    hef' (by simpa only [R] using hqiPow') (by simpa only [R] using hsjPow')
  have hjR : j < R.length := farEnd_lt_of_aligned_seam
    (by have := lt_of_lt_of_le hi2 huLen; omega) hj1 (le_trans hj hu'Len)
    hj'1 (le_trans hj' hu'Len) hpos hpos'
  have hadj : j' = j + 1 :=
    farSide_adjacent_of_matches hinj' hnodup
      (lt_of_lt_of_le (by omega : i < u.length) huLen)
      (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
      (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
      (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
      (by omega) (by omega) hjR
      (by simpa only [R] using hqiPow) (by simpa only [R] using hqiPow')
      (by rw [hef]; simpa only [R] using hsjPow)
      (by rw [hef']; simpa only [R] using hsjPow')
  have halt : b' = !b := index_alternates_of_rotate hp0
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (by simpa only [R] using hqiR) (by simpa only [R] using hqiR')
  have hvd : (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (i + 1) = vq :=
    span_eq_val_of_getElem? hqi
  have hvdm : vq ∈ D.fam b := by
    have hlet := hqlet _ (List.mem_of_getElem? hqi)
    exact hlet
  have hvk : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j' = vs' := by
    rw [hadj]
    have hget : u'[j]? = some (GGT.RelLetter.comp b' vs') := by
      simpa only [hadj, Nat.add_sub_cancel] using hsj'
    exact span_eq_val_of_getElem? hget
  have hvkm : vs' ∈ D.fam b' := by
    have hlet := hslet _ (List.mem_of_getElem? hsj')
    exact hlet
  have hgap1 := trivialGap_of_two_connectors hdisj halt hh hh' hc hc' hvd
    hvdm hvk hvkm
  exact listVal_conj_of_alignedMatch_pair hnodup hinj hsep
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
    he hf hw hw' (by omega) (by omega) hx
    (by simpa only [hjstep] using hx')
    (by simpa only [hjstep] using hgap1)
    (by simpa only [R] using hqiPow)
    (by simpa only [R] using hsjPow)

/-- The mirrored aligned branch from two adjacent published-gap matches.  W4
makes the second gap of the first match trivial, so its inverse is the first
gap of the second match, which is the gap used by the mirrored closer. -/
theorem listVal_conj_of_relativeAdjacent_revInv
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ} {ms : List ℕ}
    (hnodup : ms.Nodup)
    (hinj : ∀ b : Bool, Function.Injective (fun n : ℕ ↦ a b ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ e ∈ ms, ∀ f ∈ ms, e ≠ f → ∀ b : Bool,
      ∀ x ∈ D.relBall b eps, ∀ x' ∈ D.relBall b eps,
        x * a b ^ e * x' ≠ a b ^ f ∧ x * a b ^ e * x' ≠ (a b ^ f)⁻¹)
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {p : List G} (hp0 : 0 < p.length) {c c' i j j' : ℕ}
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c = u ++ tl)
    (hw' : (RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c' = u' ++ tl')
    (hi0 : 0 < i) (hi2 : i + 2 < u.length)
    {b b' : Bool}
    (hcomp : GGT.OsinComponents.IsComp b u i (i + 1))
    (hcomp' : GGT.OsinComponents.IsComp b' u (i + 1) (i + 2))
    (hj1 : 1 < j) (hj : j ≤ u'.length)
    (hcompS : GGT.OsinComponents.IsComp b u' (j - 1) j)
    (hj'1 : 1 < j') (hj' : j' ≤ u'.length)
    (hcompS' : GGT.OsinComponents.IsComp b' u' (j' - 1) j')
    {h h' : G} (hh : h ∈ D.fam b) (hh' : h' ∈ D.fam b')
    (hc : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u i * h =
      GGT.OsinComponents.vertex (1 : G) u' j)
    (hc' : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1) * h' =
      GGT.OsinComponents.vertex (1 : G) u' j')
    (hx : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
          ∈ D.relBall b eps)
    (hx' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j ∈ D.relBall b eps)
    (hy : (GGT.OsinComponents.vertex (1 : G) u' (j' - 1))⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1)) ∈ D.relBall b' eps)
    (hy' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 2))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j' ∈ D.relBall b' eps)
    (hqlet : ∀ x ∈ u, D.IsLetter x) (hslet : ∀ x ∈ u', D.IsLetter x) :
    GGT.RelLetter.listVal ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c') =
      GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal ((RelWord.revInv
          (relatorWord₂ p (a false) (a true) ms)).rotate c) *
          (GGT.RelLetter.listVal py)⁻¹ := by
  let R := RelWord.revInv (relatorWord₂ p (a false) (a true) ms)
  have huLen : u.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'Len : u'.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hqOf := hcomp.2.2.1 i le_rfl (by omega) (by omega)
  obtain ⟨vq, hqi⟩ := getElem?_comp_of_isCompOf (by omega) hqOf
  have hqOf' := hcomp'.2.2.1 (i + 1) le_rfl (by omega) (by omega)
  obtain ⟨vq', hqi'⟩ := getElem?_comp_of_isCompOf (by omega) hqOf'
  have hsOf := hcompS.2.2.1 (j - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs, hsj⟩ := getElem?_comp_of_isCompOf (by omega) hsOf
  have hsOf' := hcompS'.2.2.1 (j' - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs', hsj'⟩ := getElem?_comp_of_isCompOf (by omega) hsOf'
  have hqiR : (R.rotate c)[i]? = some (GGT.RelLetter.comp b vq) := by
    rw [hw, List.getElem?_append_left (by omega : i < u.length)]
    exact hqi
  have hqiR' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b' vq') := by
    rw [hw, List.getElem?_append_left (by omega : i + 1 < u.length)]
    exact hqi'
  have hsjR : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b vs) := by
    rw [hw', List.getElem?_append_left (by omega : j - 1 < u'.length)]
    exact hsj
  have hsjR' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b' vs') := by
    rw [hw', List.getElem?_append_left (by omega : j' - 1 < u'.length)]
    exact hsj'
  obtain ⟨e, he, hvq⟩ := exponent_of_comp_rotate_revInv hqiR
  obtain ⟨e', he', hvq'⟩ := exponent_of_comp_rotate_revInv hqiR'
  obtain ⟨f, hf, hvs⟩ := exponent_of_comp_rotate_revInv hsjR
  obtain ⟨f', hf', hvs'⟩ := exponent_of_comp_rotate_revInv hsjR'
  have hqiPow : (R.rotate c)[i]? = some (GGT.RelLetter.comp b
      (((if b then a true else a false) ^ e)⁻¹)) := by
    simpa only [hvq] using hqiR
  have hqiPow' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b'
      (((if b' then a true else a false) ^ e')⁻¹)) := by
    simpa only [hvq'] using hqiR'
  have hsjPow : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b
      (((if b then a true else a false) ^ f)⁻¹)) := by
    simpa only [hvs] using hsjR
  have hsjPow' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b'
      (((if b' then a true else a false) ^ f')⁻¹)) := by
    simpa only [hvs'] using hsjR'
  have hrel := conj_of_matchedPair_letters (py := py) hqi hsj
  have hrel' := conj_of_matchedPair_letters (py := py) hqi' hsj'
  rw [hvq, hvs, ite_apply_eq a b] at hrel
  rw [hvq', hvs', ite_apply_eq a b'] at hrel'
  have hjstep : j - 1 + 1 = j := by omega
  have hj'step : j' - 1 + 1 = j' := by omega
  rw [hjstep] at hrel
  rw [hj'step] at hrel'
  have hef : e = f := exponent_eq_of_mirroredPair_ball hsymm hsep he hf hx hx' hrel
  have hef' : e' = f' :=
    exponent_eq_of_mirroredPair_ball hsymm hsep he' hf' hy hy' hrel'
  have hinj' : ∀ t : Bool, Function.Injective
      (fun n : ℕ ↦ (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  have hpos := position_eq_of_alignedMatch_revInv hinj' hnodup
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
    hef (by simpa only [R] using hqiPow) (by simpa only [R] using hsjPow)
  have hpos' := position_eq_of_alignedMatch_revInv hinj' hnodup
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
    hef' (by simpa only [R] using hqiPow') (by simpa only [R] using hsjPow')
  have hjR : j < R.length := farEnd_lt_of_aligned_seam
    (by have := lt_of_lt_of_le hi2 huLen; omega) hj1 (le_trans hj hu'Len)
    hj'1 (le_trans hj' hu'Len) hpos hpos'
  have hadj : j' = j + 1 :=
    farSide_adjacent_of_matches_revInv hinj' hnodup
      (lt_of_lt_of_le (by omega : i < u.length) huLen)
      (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
      (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
      (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
      (by omega) (by omega) hjR
      (by simpa only [R] using hqiPow) (by simpa only [R] using hqiPow')
      (by rw [hef]; simpa only [R] using hsjPow)
      (by rw [hef']; simpa only [R] using hsjPow')
  have halt : b' = !b := index_alternates_of_rotate_revInv hp0
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (by simpa only [R] using hqiR) (by simpa only [R] using hqiR')
  have hvd : (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (i + 1) = vq :=
    span_eq_val_of_getElem? hqi
  have hvdm : vq ∈ D.fam b := hqlet _ (List.mem_of_getElem? hqi)
  have hvk : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j' = vs' := by
    rw [hadj]
    have hget : u'[j]? = some (GGT.RelLetter.comp b' vs') := by
      simpa only [hadj, Nat.add_sub_cancel] using hsj'
    exact span_eq_val_of_getElem? hget
  have hvkm : vs' ∈ D.fam b' := hslet _ (List.mem_of_getElem? hsj')
  have hgap1 := trivialGap_of_two_connectors hdisj halt hh hh' hc hc' hvd
    hvdm hvk hvkm
  have hgap0' : (GGT.OsinComponents.vertex (1 : G) u' (j' - 1))⁻¹ *
      (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1)) = 1 := by
    have hinv := congrArg (fun g : G ↦ g⁻¹) hgap1
    rw [inv_one, mul_inv_rev, inv_inv] at hinv
    have hjstart : j' - 1 = j := by omega
    rw [hjstart]
    exact hinv
  exact listVal_conj_of_mirroredAlignedMatch_pair hnodup hinj hsymm hsep
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
    he' hf' hw hw' (by omega) (by omega) hy
    (by simpa only [hj'step] using hy') hgap0'
    (by simpa only [R] using hqiPow')
    (by simpa only [R] using hsjPow')

end Aligned

section Mixed

variable {G : Type u} [Group G]

/-- Pin the exponent when the source is mirrored and the target is direct.
Inverting the matched-pair relation puts it in the existing mirrored-ball
shape; symmetry preserves the two ball memberships. -/
theorem exponent_eq_of_reverseMirroredBlockMatch_ball
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps : ℕ} {ms : List ℕ}
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ e ∈ ms, ∀ f ∈ ms, e ≠ f → ∀ b : Bool,
      ∀ x ∈ D.relBall b eps, ∀ x' ∈ D.relBall b eps,
        x * a b ^ e * x' ≠ a b ^ f ∧ x * a b ^ e * x' ≠ (a b ^ f)⁻¹)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms) {x x' : G}
    (hx : x ∈ D.relBall b eps) (hx' : x' ∈ D.relBall b eps)
    (hrel : x * (a b ^ e)⁻¹ * x' = a b ^ f) : e = f := by
  have hinvrel : x'⁻¹ * a b ^ e * x⁻¹ = (a b ^ f)⁻¹ := by
    have h := congrArg (fun g : G ↦ g⁻¹) hrel
    simpa [mul_inv_rev, mul_assoc] using h
  exact exponent_eq_of_mirroredBlockMatch_ball hsep he hf
    (inv_mem_relBall hsymm hx') (inv_mem_relBall hsymm hx) hinvrel

/-- The direct-to-mirrored branch is impossible from two adjacent
published-gap matches.  Reflection reverses the two far components; W4 then
makes the middle connector trivial and exposes the inverse of a design power
as the first match's second bounded gap. -/
theorem false_of_relativeAdjacent_direct_revInv
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps rho : ℕ} {ms : List ℕ}
    (hnodup : ms.Nodup)
    (hinj : ∀ b : Bool, Function.Injective (fun n : ℕ ↦ a b ^ n))
    (hsep : ∀ e ∈ ms, ∀ f ∈ ms, e ≠ f → ∀ b : Bool,
      ∀ x ∈ D.relBall b eps, ∀ x' ∈ D.relBall b eps,
        x * a b ^ e * x' ≠ a b ^ f ∧ x * a b ^ e * x' ≠ (a b ^ f)⁻¹)
    (hdeep : ∀ e ∈ ms, ∀ b : Bool,
      a b ^ e ∉ D.relBall b rho ∧ (a b ^ e)⁻¹ ∉ D.relBall b rho)
    (hepsrho : eps ≤ rho)
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {p : List G} (hp0 : 0 < p.length) {c c' i j j' : ℕ}
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c' = u' ++ tl')
    (hi0 : 0 < i) (hi2 : i + 2 < u.length)
    {b b' : Bool}
    (hcomp : GGT.OsinComponents.IsComp b u i (i + 1))
    (hcomp' : GGT.OsinComponents.IsComp b' u (i + 1) (i + 2))
    (hj1 : 1 < j) (hj : j ≤ u'.length)
    (hcompS : GGT.OsinComponents.IsComp b u' (j - 1) j)
    (hj'1 : 1 < j') (hj' : j' ≤ u'.length)
    (hcompS' : GGT.OsinComponents.IsComp b' u' (j' - 1) j')
    {h h' : G} (hh : h ∈ D.fam b) (hh' : h' ∈ D.fam b')
    (hc : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u i * h =
      GGT.OsinComponents.vertex (1 : G) u' j)
    (hc' : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1) * h' =
      GGT.OsinComponents.vertex (1 : G) u' j')
    (hx : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
          ∈ D.relBall b eps)
    (hx' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j ∈ D.relBall b eps)
    (hy : (GGT.OsinComponents.vertex (1 : G) u' (j' - 1))⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1)) ∈ D.relBall b' eps)
    (hy' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 2))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j' ∈ D.relBall b' eps)
    (hqlet : ∀ x ∈ u, D.IsLetter x) : False := by
  let R := relatorWord₂ p (a false) (a true) ms
  have huLen : u.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'Len : u'.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw'
    rw [List.length_rotate, RelWord.length_revInv, List.length_append] at hL
    omega
  have hqOf := hcomp.2.2.1 i le_rfl (by omega) (by omega)
  obtain ⟨vq, hqi⟩ := getElem?_comp_of_isCompOf (by omega) hqOf
  have hqOf' := hcomp'.2.2.1 (i + 1) le_rfl (by omega) (by omega)
  obtain ⟨vq', hqi'⟩ := getElem?_comp_of_isCompOf (by omega) hqOf'
  have hsOf := hcompS.2.2.1 (j - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs, hsj⟩ := getElem?_comp_of_isCompOf (by omega) hsOf
  have hsOf' := hcompS'.2.2.1 (j' - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs', hsj'⟩ := getElem?_comp_of_isCompOf (by omega) hsOf'
  have hqiR : (R.rotate c)[i]? = some (GGT.RelLetter.comp b vq) := by
    rw [hw, List.getElem?_append_left (by omega : i < u.length)]
    exact hqi
  have hqiR' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b' vq') := by
    rw [hw, List.getElem?_append_left (by omega : i + 1 < u.length)]
    exact hqi'
  have hsjR : ((RelWord.revInv R).rotate c')[j - 1]? =
      some (GGT.RelLetter.comp b vs) := by
    rw [hw', List.getElem?_append_left (by omega : j - 1 < u'.length)]
    exact hsj
  have hsjR' : ((RelWord.revInv R).rotate c')[j' - 1]? =
      some (GGT.RelLetter.comp b' vs') := by
    rw [hw', List.getElem?_append_left (by omega : j' - 1 < u'.length)]
    exact hsj'
  obtain ⟨e, he, hvq⟩ := exponent_of_comp_rotate hqiR
  obtain ⟨e', he', hvq'⟩ := exponent_of_comp_rotate hqiR'
  obtain ⟨f, hf, hvs⟩ := exponent_of_comp_rotate_revInv hsjR
  obtain ⟨f', hf', hvs'⟩ := exponent_of_comp_rotate_revInv hsjR'
  have hqiPow : (R.rotate c)[i]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ e)) := by
    simpa only [hvq] using hqiR
  have hqiPow' : (R.rotate c)[i + 1]? = some (GGT.RelLetter.comp b'
      ((if b' then a true else a false) ^ e')) := by
    simpa only [hvq'] using hqiR'
  have hsjPow : ((RelWord.revInv R).rotate c')[j - 1]? =
      some (GGT.RelLetter.comp b (((if b then a true else a false) ^ f)⁻¹)) := by
    simpa only [hvs] using hsjR
  have hsjPow' : ((RelWord.revInv R).rotate c')[j' - 1]? =
      some (GGT.RelLetter.comp b' (((if b' then a true else a false) ^ f')⁻¹)) := by
    simpa only [hvs'] using hsjR'
  have hrel := conj_of_matchedPair_letters (py := py) hqi hsj
  have hrel' := conj_of_matchedPair_letters (py := py) hqi' hsj'
  rw [hvq, hvs, ite_apply_eq a b] at hrel
  rw [hvq', hvs', ite_apply_eq a b'] at hrel'
  have hjstep : j - 1 + 1 = j := by omega
  have hj'step : j' - 1 + 1 = j' := by omega
  rw [hjstep] at hrel
  rw [hj'step] at hrel'
  have hef : e = f := exponent_eq_of_mirroredBlockMatch_ball hsep he hf hx hx' hrel
  have hef' : e' = f' :=
    exponent_eq_of_mirroredBlockMatch_ball hsep he' hf' hy hy' hrel'
  have hinj' : ∀ t : Bool, Function.Injective
      (fun n : ℕ ↦ (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  have hsum := position_sum_of_mirroredMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
    hef (by simpa only [R] using hqiPow) (by simpa only [R] using hsjPow)
  have hsum' := position_sum_of_mirroredMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
    hef' (by simpa only [R] using hqiPow') (by simpa only [R] using hsjPow')
  have hpred : j = j' + 1 := farEnd_pred_of_mirrored_seam
    (by have := lt_of_lt_of_le hi2 huLen; omega) hj1 (le_trans hj hu'Len)
    hj'1 (le_trans hj' hu'Len) hsum hsum'
  have halt : b' = !b := index_alternates_of_rotate hp0
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (by simpa only [R] using hqiR) (by simpa only [R] using hqiR')
  have hAB : (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (i + 1) = a b ^ e := by
    rw [span_eq_val_of_getElem? hqi, hvq, ite_apply_eq a b]
    rfl
  have hVW0 := span_eq_val_of_getElem? hsj
  rw [hvs, ite_apply_eq a b, ← hef] at hVW0
  have hVW : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j = (a b ^ e)⁻¹ := by
    simpa only [hjstep] using hVW0
  have hg : a b ^ e ∈ D.fam b := by
    rw [← hAB]
    exact hqlet _ (List.mem_of_getElem? hqi)
  have hjstart : j' = j - 1 := by omega
  have hmiddle : h' = 1 := reverseAdjacent_connector_eq_one hdisj halt hg hh hh'
    hAB hVW hc (by simpa only [hjstart] using hc')
  have hgapPower : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j = (a b ^ e)⁻¹ :=
    secondGap_eq_of_reverseAdjacent
      (by simpa only [hjstart] using hc') hmiddle hVW
  have hball : (a b ^ e)⁻¹ ∈ D.relBall b rho := by
    rw [← hgapPower]
    exact GGT.OsinComponents.relBall_mono_radius D b hepsrho hx'
  exact (hdeep e he b).2 hball

/-- The mirrored-to-direct branch is impossible by the same reverse-adjacent
W4 calculation.  Here the bounded second gap is the positive design power. -/
theorem false_of_relativeAdjacent_revInv_direct
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps rho : ℕ} {ms : List ℕ}
    (hnodup : ms.Nodup)
    (hinj : ∀ b : Bool, Function.Injective (fun n : ℕ ↦ a b ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ e ∈ ms, ∀ f ∈ ms, e ≠ f → ∀ b : Bool,
      ∀ x ∈ D.relBall b eps, ∀ x' ∈ D.relBall b eps,
        x * a b ^ e * x' ≠ a b ^ f ∧ x * a b ^ e * x' ≠ (a b ^ f)⁻¹)
    (hdeep : ∀ e ∈ ms, ∀ b : Bool,
      a b ^ e ∉ D.relBall b rho ∧ (a b ^ e)⁻¹ ∉ D.relBall b rho)
    (hepsrho : eps ≤ rho)
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {p : List G} (hp0 : 0 < p.length) {c c' i j j' : ℕ}
    {py u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hi0 : 0 < i) (hi2 : i + 2 < u.length)
    {b b' : Bool}
    (hcomp : GGT.OsinComponents.IsComp b u i (i + 1))
    (hcomp' : GGT.OsinComponents.IsComp b' u (i + 1) (i + 2))
    (hj1 : 1 < j) (hj : j ≤ u'.length)
    (hcompS : GGT.OsinComponents.IsComp b u' (j - 1) j)
    (hj'1 : 1 < j') (hj' : j' ≤ u'.length)
    (hcompS' : GGT.OsinComponents.IsComp b' u' (j' - 1) j')
    {h h' : G} (hh : h ∈ D.fam b) (hh' : h' ∈ D.fam b')
    (hc : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u i * h =
      GGT.OsinComponents.vertex (1 : G) u' j)
    (hc' : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1) * h' =
      GGT.OsinComponents.vertex (1 : G) u' j')
    (hx : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
        (GGT.RelLetter.listVal py * GGT.OsinComponents.vertex (1 : G) u i)
          ∈ D.relBall b eps)
    (hx' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j ∈ D.relBall b eps)
    (hy : (GGT.OsinComponents.vertex (1 : G) u' (j' - 1))⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u (i + 1)) ∈ D.relBall b' eps)
    (hy' : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 2))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' j' ∈ D.relBall b' eps)
    (hqlet : ∀ x ∈ u, D.IsLetter x) : False := by
  let R := relatorWord₂ p (a false) (a true) ms
  have huLen : u.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw
    rw [List.length_rotate, RelWord.length_revInv, List.length_append] at hL
    omega
  have hu'Len : u'.length ≤ R.length := by
    dsimp only [R]
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hqOf := hcomp.2.2.1 i le_rfl (by omega) (by omega)
  obtain ⟨vq, hqi⟩ := getElem?_comp_of_isCompOf (by omega) hqOf
  have hqOf' := hcomp'.2.2.1 (i + 1) le_rfl (by omega) (by omega)
  obtain ⟨vq', hqi'⟩ := getElem?_comp_of_isCompOf (by omega) hqOf'
  have hsOf := hcompS.2.2.1 (j - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs, hsj⟩ := getElem?_comp_of_isCompOf (by omega) hsOf
  have hsOf' := hcompS'.2.2.1 (j' - 1) le_rfl (by omega) (by omega)
  obtain ⟨vs', hsj'⟩ := getElem?_comp_of_isCompOf (by omega) hsOf'
  have hqiR : ((RelWord.revInv R).rotate c)[i]? =
      some (GGT.RelLetter.comp b vq) := by
    rw [hw, List.getElem?_append_left (by omega : i < u.length)]
    exact hqi
  have hqiR' : ((RelWord.revInv R).rotate c)[i + 1]? =
      some (GGT.RelLetter.comp b' vq') := by
    rw [hw, List.getElem?_append_left (by omega : i + 1 < u.length)]
    exact hqi'
  have hsjR : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b vs) := by
    rw [hw', List.getElem?_append_left (by omega : j - 1 < u'.length)]
    exact hsj
  have hsjR' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b' vs') := by
    rw [hw', List.getElem?_append_left (by omega : j' - 1 < u'.length)]
    exact hsj'
  obtain ⟨e, he, hvq⟩ := exponent_of_comp_rotate_revInv hqiR
  obtain ⟨e', he', hvq'⟩ := exponent_of_comp_rotate_revInv hqiR'
  obtain ⟨f, hf, hvs⟩ := exponent_of_comp_rotate hsjR
  obtain ⟨f', hf', hvs'⟩ := exponent_of_comp_rotate hsjR'
  have hqiPow : ((RelWord.revInv R).rotate c)[i]? =
      some (GGT.RelLetter.comp b (((if b then a true else a false) ^ e)⁻¹)) := by
    simpa only [hvq] using hqiR
  have hqiPow' : ((RelWord.revInv R).rotate c)[i + 1]? =
      some (GGT.RelLetter.comp b' (((if b' then a true else a false) ^ e')⁻¹)) := by
    simpa only [hvq'] using hqiR'
  have hsjPow : (R.rotate c')[j - 1]? = some (GGT.RelLetter.comp b
      ((if b then a true else a false) ^ f)) := by
    simpa only [hvs] using hsjR
  have hsjPow' : (R.rotate c')[j' - 1]? = some (GGT.RelLetter.comp b'
      ((if b' then a true else a false) ^ f')) := by
    simpa only [hvs'] using hsjR'
  have hrel := conj_of_matchedPair_letters (py := py) hqi hsj
  have hrel' := conj_of_matchedPair_letters (py := py) hqi' hsj'
  rw [hvq, hvs, ite_apply_eq a b] at hrel
  rw [hvq', hvs', ite_apply_eq a b'] at hrel'
  have hjstep : j - 1 + 1 = j := by omega
  have hj'step : j' - 1 + 1 = j' := by omega
  rw [hjstep] at hrel
  rw [hj'step] at hrel'
  have hef : e = f :=
    exponent_eq_of_reverseMirroredBlockMatch_ball hsymm hsep he hf hx hx' hrel
  have hef' : e' = f' :=
    exponent_eq_of_reverseMirroredBlockMatch_ball hsymm hsep he' hf' hy hy' hrel'
  have hinj' : ∀ t : Bool, Function.Injective
      (fun n : ℕ ↦ (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  have hsum0 := position_sum_of_mirroredMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : j - 1 < u'.length) hu'Len)
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    hef (by rw [hef]; simpa only [R] using hsjPow)
      (by simpa only [R] using hqiPow)
  have hsum1 := position_sum_of_mirroredMatch hinj' hnodup
    (lt_of_lt_of_le (by omega : j' - 1 < u'.length) hu'Len)
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    hef' (by rw [hef']; simpa only [R] using hsjPow')
      (by simpa only [R] using hqiPow')
  have hsum : (c + i) % R.length + (c' + (j - 1)) % R.length =
      R.length - 1 := by simpa only [Nat.add_comm] using hsum0
  have hsum' : (c + (i + 1)) % R.length + (c' + (j' - 1)) % R.length =
      R.length - 1 := by simpa only [Nat.add_comm] using hsum1
  have hpred : j = j' + 1 := farEnd_pred_of_mirrored_seam
    (by have := lt_of_lt_of_le hi2 huLen; omega) hj1 (le_trans hj hu'Len)
    hj'1 (le_trans hj' hu'Len) hsum hsum'
  have halt : b' = !b := index_alternates_of_rotate_revInv hp0
    (lt_of_lt_of_le (by omega : i < u.length) huLen)
    (lt_of_lt_of_le (by omega : i + 1 < u.length) huLen)
    (by simpa only [R] using hqiR) (by simpa only [R] using hqiR')
  have hAB : (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (i + 1) = (a b ^ e)⁻¹ := by
    rw [span_eq_val_of_getElem? hqi, hvq, ite_apply_eq a b]
    rfl
  have hVW0 := span_eq_val_of_getElem? hsj
  rw [hvs, ite_apply_eq a b, ← hef] at hVW0
  have hVW : (GGT.OsinComponents.vertex (1 : G) u' (j - 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j = a b ^ e := by
    simpa only [hjstep] using hVW0
  have hg : (a b ^ e)⁻¹ ∈ D.fam b := by
    rw [← hAB]
    exact hqlet _ (List.mem_of_getElem? hqi)
  have hjstart : j' = j - 1 := by omega
  have hmiddle : h' = 1 := reverseAdjacent_connector_eq_one hdisj halt hg hh hh'
    hAB hVW hc (by simpa only [hjstart] using hc')
  have hgapPower : (GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u (i + 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' j = a b ^ e := by
    have h := secondGap_eq_of_reverseAdjacent
      (by simpa only [hjstart] using hc') hmiddle hVW
    simpa only [inv_inv] using h
  have hball : a b ^ e ∈ D.relBall b rho := by
    rw [← hgapPower]
    exact GGT.OsinComponents.relBall_mono_radius D b hepsrho hx'
  exact (hdeep e he b).1 hball

end Mixed

section FourWay

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- The relative-side four-way closer for an exact design.  The adjacent-gap
package supplies all four bounded gaps and both connectors.  The two aligned
branches use W4 to trivialise the shared gap; the two mixed branches use the
reverse-adjacent contradiction. -/
theorem listVal_conj_of_exactPublished_relativeSides
    (E : HypEmbeddedCore₂ A N)
    {epsD designRho diffRadius W target adjacentC bn : ℕ}
    {baseLetter : G} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter designRho epsD
      diffRadius W target ms)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1)
    (heven : Even ms.length)
    (hW : 1 + blockConst [baseLetter] 1 ≤ W)
    (hadj : ExactPublishedAdjacentGapOutput E adjacentC bn)
    (hadjRho : adjacentC * 4 ≤ designRho)
    (hadjEps : adjacentC * 4 ≤ epsD)
    (hepsRho : epsD ≤ designRho)
    {w w' u u' tl tl' py pz : List (GGT.RelLetter G Bool)}
    (hw : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w)
    (hw' : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) w')
    (hu : w = u ++ tl) (hu' : w' = u' ++ tl')
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hpz0 : 0 < pz.length)
    (hlet4 : ∀ x ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      E.rel.IsLetter x)
    (hqg : ∀ t : ℕ, t < 4 → ∀ x y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ x → x ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ) ≤
        ((wordDist E.rel.alphabet.carrier
          (GGT.OsinComponents.vertex (1 : G)
            (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') x)
          (GGT.OsinComponents.vertex (1 : G)
            (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hlen : 2 * (py.length + pz.length + 3) + 2 ≤ u.length)
    (hqlet : ∀ x ∈ u, E.rel.IsLetter x)
    (hslet : ∀ x ∈ u', E.rel.IsLetter x) :
    GGT.RelLetter.listVal w' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal w * (GGT.RelLetter.listVal py)⁻¹ := by
  have hsymm : ∀ g ∈ E.rel.base, g⁻¹ ∈ E.rel.base :=
    fun g hg ↦ (isSymmetricGeneratingSet_base₂ E).inv_mem g hg
  have hdisj : ∀ x : G, x ∈ E.rel.fam false →
      x ∈ E.rel.fam true → x = 1 := by
    rw [E.fam_eq]
    exact E.disjoint
  have hdeep : ∀ e ∈ ms, ∀ b : Bool,
      E.lox b ^ e ∉ E.rel.relBall b designRho ∧
        (E.lox b ^ e)⁻¹ ∉ E.rel.relBall b designRho :=
    fun e he b ↦ hdesign.2.2.1 e he b b
  refine listVal_conj_of_sym_cases hw hw' ?_ ?_ ?_ ?_
  · intro c c' hc hc'
    subst hc
    subst hc'
    obtain ⟨b, b', i, j, j', hi0, hi2, hcomp, hcomp', hj1, hj,
        hcompS, hj'1, hj', hcompS', ⟨h, hh, hconn⟩, ⟨h', hh', hconn'⟩,
        hx, hx', hy, hy'⟩ :=
      hadj hdesign hcount heven hW
        (RelWord.Sym.rot c RelWord.Sym.base) hu
        (RelWord.Sym.rot c' RelWord.Sym.base) hu'
        py pz hclose hpz0 hlet4 hqg hadjRho hadjEps hlen
    exact listVal_conj_of_relativeAdjacent_direct hdesign.2.1
      (injective_pow_lox₂ E) hdesign.2.2.2.1 hdisj (by simp)
      hu hu' hi0 hi2 hcomp hcomp' hj1 hj hcompS hj'1 hj' hcompS'
      hh hh' hconn hconn' hx hx' hy hy' hqlet hslet
  · intro c c' hc hc'
    subst hc
    subst hc'
    obtain ⟨b, b', i, j, j', hi0, hi2, hcomp, hcomp', hj1, hj,
        hcompS, hj'1, hj', hcompS', ⟨h, hh, hconn⟩, ⟨h', hh', hconn'⟩,
        hx, hx', hy, hy'⟩ :=
      hadj hdesign hcount heven hW
        (RelWord.Sym.rot c (RelWord.Sym.inv RelWord.Sym.base)) hu
        (RelWord.Sym.rot c' (RelWord.Sym.inv RelWord.Sym.base)) hu'
        py pz hclose hpz0 hlet4 hqg hadjRho hadjEps hlen
    exact listVal_conj_of_relativeAdjacent_revInv hdesign.2.1
      (injective_pow_lox₂ E) hsymm hdesign.2.2.2.1 hdisj (by simp)
      hu hu' hi0 hi2 hcomp hcomp' hj1 hj hcompS hj'1 hj' hcompS'
      hh hh' hconn hconn' hx hx' hy hy' hqlet hslet
  · intro c c' hc hc'
    subst hc
    subst hc'
    obtain ⟨b, b', i, j, j', hi0, hi2, hcomp, hcomp', hj1, hj,
        hcompS, hj'1, hj', hcompS', ⟨h, hh, hconn⟩, ⟨h', hh', hconn'⟩,
        hx, hx', hy, hy'⟩ :=
      hadj hdesign hcount heven hW
        (RelWord.Sym.rot c RelWord.Sym.base) hu
        (RelWord.Sym.rot c' (RelWord.Sym.inv RelWord.Sym.base)) hu'
        py pz hclose hpz0 hlet4 hqg hadjRho hadjEps hlen
    exact false_of_relativeAdjacent_direct_revInv hdesign.2.1
      (injective_pow_lox₂ E) hdesign.2.2.2.1 hdeep hepsRho hdisj (by simp)
      hu hu' hi0 hi2 hcomp hcomp' hj1 hj hcompS hj'1 hj' hcompS'
      hh hh' hconn hconn' hx hx' hy hy' hqlet
  · intro c c' hc hc'
    subst hc
    subst hc'
    obtain ⟨b, b', i, j, j', hi0, hi2, hcomp, hcomp', hj1, hj,
        hcompS, hj'1, hj', hcompS', ⟨h, hh, hconn⟩, ⟨h', hh', hconn'⟩,
        hx, hx', hy, hy'⟩ :=
      hadj hdesign hcount heven hW
        (RelWord.Sym.rot c (RelWord.Sym.inv RelWord.Sym.base)) hu
        (RelWord.Sym.rot c' RelWord.Sym.base) hu'
        py pz hclose hpz0 hlet4 hqg hadjRho hadjEps hlen
    exact false_of_relativeAdjacent_revInv_direct hdesign.2.1
      (injective_pow_lox₂ E) hsymm hdesign.2.2.2.1 hdeep hepsRho hdisj
      (by simp) hu hu' hi0 hi2 hcomp hcomp' hj1 hj hcompS hj'1 hj'
      hcompS' hh hh' hconn hconn' hx hx' hy hy' hqlet

end FourWay

end HullSC
end GroupApproximation
