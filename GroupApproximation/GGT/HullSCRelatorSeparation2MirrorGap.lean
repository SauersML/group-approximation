import GroupApproximation.GGT.HullSCRelatorSeparation2Locate

/-!
# The mixed case of step (c), in the form the polygon estimate delivers

`GGT/HullSCRelatorSeparation2MirrorRun.lean` closes the mixed case from two
blocks matched at *adjacent* positions of the run.  Adjacency is more than the
polygon estimate gives: what it gives is a pair of matched blocks with the two
gaps close to one another, and the offsets of a rotation need not be positions
of the run at all.  This module is the same exclusion from that weaker input,
and it is the one the assembly uses.

The whole content is one identity.  Write `n` for the length of the relator and
read a rotation at an offset: `π(i) = (c + i) % n` is the position it reads.  A
matched block in the mixed case -- one member a rotation of the relator, the
other a rotation of its formal inverse -- forces, through the mirrored rigidity
and repetition-freeness of the exponents,

  `π(i) + π'(j) = n - 1`,

because the run index counted from the left and the run index counted from the
right add up to the whole run.  That is `position_sum_of_mirroredMatch`.

Two matched pairs subtract.  Modulo `n` the shifts cancel, leaving
`(i₂ - i₁) + (j₂ - j₁) ≡ 0`, and both gaps are positive and below `n`, so the
two gaps **sum to `n` exactly** (`gap_sum_of_mirrored`).  The estimate says the
two gaps are within `2(ε+1)` of each other, so `n` is at most twice the first
gap plus `2(ε+1)`; choosing the two deep blocks with a gap small against the
length of the relator contradicts it.  The choice is free: the gap is bounded
below by the estimate and above by nothing, and `n` grows with the number of
exponents.

Nothing here mentions arcs, adjacency or the wrap-around: the modular arithmetic
absorbs all three.  That is why this form, and not the adjacent one, is what the
polygon leaf should be asked for.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **A displacement congruent to zero and below twice the modulus is the
modulus.** -/
theorem eq_of_modEq_add {n d u : ℕ} (_hn : 0 < n) (hd : 0 < d) (hd2 : d < 2 * n)
    (h : u ≡ u + d [MOD n]) : d = n := by
  have hdvd : n ∣ u + d - u :=
    (Nat.modEq_iff_dvd' (Nat.le_add_right u d)).mp h
  rw [show u + d - u = d from by omega] at hdvd
  obtain ⟨m, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [Nat.mul_zero] at hd
    exact absurd hd (Nat.lt_irrefl 0)
  · have hlt : n * m < n * 2 := by omega
    have hm2 : m < 2 := Nat.lt_of_mul_lt_mul_left hlt
    have hm1 : m = 1 := by omega
    rw [hm1, Nat.mul_one]

section Gap

variable {G : Type u} [Group G]

/-- **The two positions of a mirrored match add up to the length.**

The block read at offset `i` of a rotation of the relator sits at run index
`π(i) - |p|`; the block read at offset `j` of a rotation of the formal inverse
sits at run index `|ms| - 1 - π'(j)`.  Equal exponents and repetition-freeness
identify the two, and the identity follows from `|R| = |p| + |ms|`. -/
theorem position_sum_of_mirroredMatch {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p h₀ h₁ ms).length)
    (hj : j < (relatorWord₂ p h₀ h₁ ms).length)
    {b b' : Bool} {e f : ℕ} (hef : e = f)
    (hxi : ((relatorWord₂ p h₀ h₁ ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ e)))
    (hxj : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b' (((if b' then h₁ else h₀) ^ f)⁻¹))) :
    (c + i) % (relatorWord₂ p h₀ h₁ ms).length
        + (c' + j) % (relatorWord₂ p h₀ h₁ ms).length
      = (relatorWord₂ p h₀ h₁ ms).length - 1 := by
  have hrev : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = (relatorWord₂ p h₀ h₁ ms).length := RelWord.length_revInv _
  have hlen : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  have h1 := getElem?_of_rotate hi hxi
  have hj' : j < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
    rw [hrev]
    exact hj
  have h2 := getElem?_of_rotate hj' hxj
  rw [hrev] at h2
  obtain ⟨k, hkeq, hklt, hkb⟩ := blockIndex_of_relatorWord₂ h1
  obtain ⟨htlt, htb⟩ := blockIndex_of_revInv_relatorWord₂ h2
  obtain ⟨m, hm, hme⟩ := blockWord_getElem?_exponent h₀ h₁ false ms k b _ hkb
  obtain ⟨m', hm', hm'e⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ false ms
      (q := ms.length - 1 - (c' + j) % (relatorWord₂ p h₀ h₁ ms).length)
      (by omega) htb
  have hem : e = m := hinj b hme
  have hfm : f = m' := hinj b' (inv_injective hm'e)
  have hmm : m = m' := by omega
  rw [hmm] at hm
  have hkr : k = ms.length - 1
      - (c' + j) % (relatorWord₂ p h₀ h₁ ms).length :=
    getElem?_eq_of_nodup hnodup hm hm'
  omega

/-- **The two gaps of a mirrored double match sum to the length of the
relator.**  Modulo the length the two shifts cancel, and both gaps are positive
and below the length. -/
theorem gap_sum_of_mirrored {n c c' i₁ i₂ j₁ j₂ : ℕ} (hn : 0 < n)
    (hii : i₁ < i₂) (hjj : j₁ < j₂) (hin : i₂ < n) (hjn : j₂ < n)
    (hs₁ : (c + i₁) % n + (c' + j₁) % n = n - 1)
    (hs₂ : (c + i₂) % n + (c' + j₂) % n = n - 1) :
    i₂ - i₁ + (j₂ - j₁) = n := by
  have hS₁ : (c + i₁ + (c' + j₁)) % n = (n - 1) % n := by
    rw [Nat.add_mod, hs₁]
  have hS₂ : (c + i₂ + (c' + j₂)) % n = (n - 1) % n := by
    rw [Nat.add_mod, hs₂]
  have hE : c + c' + (i₁ + j₁) ≡ c + c' + (i₂ + j₂) [MOD n] := by
    show (c + c' + (i₁ + j₁)) % n = (c + c' + (i₂ + j₂)) % n
    rw [show c + c' + (i₁ + j₁) = c + i₁ + (c' + j₁) from by omega,
      show c + c' + (i₂ + j₂) = c + i₂ + (c' + j₂) from by omega, hS₁, hS₂]
  have hE' : i₁ + j₁ ≡ i₂ + j₂ [MOD n] := Nat.ModEq.add_left_cancel' _ hE
  rw [show i₂ + j₂ = i₁ + j₁ + (i₂ - i₁ + (j₂ - j₁)) from by omega] at hE'
  exact eq_of_modEq_add hn (by omega) (by omega) hE'

/-- **The mixed case of step (c), from the polygon estimate.**

Two matched blocks, the second gap within `s` of the first, and the first gap
small against the length of the relator.  `s` is the estimate's `2(ε+1)`; the
inequality `2g + s < |R|` is the design's, and it is met by taking the number of
exponents large. -/
theorem not_mirroredMatch_of_gap {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' i₁ i₂ j₁ j₂ s : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p h₀ h₁ ms).length)
    (hj₂ : j₂ < (relatorWord₂ p h₀ h₁ ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₁' b₂ b₂' : Bool} {e₁ f₁ e₂ f₂ : ℕ} (hef₁ : e₁ = f₁) (hef₂ : e₂ = f₂)
    (hx₁ : ((relatorWord₂ p h₀ h₁ ms).rotate c)[i₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then h₁ else h₀) ^ e₁)))
    (hy₁ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[j₁]?
      = some (GGT.RelLetter.comp b₁' (((if b₁' then h₁ else h₀) ^ f₁)⁻¹)))
    (hx₂ : ((relatorWord₂ p h₀ h₁ ms).rotate c)[i₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then h₁ else h₀) ^ e₂)))
    (hy₂ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[j₂]?
      = some (GGT.RelLetter.comp b₂' (((if b₂' then h₁ else h₀) ^ f₂)⁻¹)))
    (hclose : j₂ - j₁ ≤ i₂ - i₁ + s)
    (hsmall : 2 * (i₂ - i₁) + s < (relatorWord₂ p h₀ h₁ ms).length) : False := by
  have hs₁ := position_sum_of_mirroredMatch hinj hnodup (by omega) (by omega)
    hef₁ hx₁ hy₁
  have hs₂ := position_sum_of_mirroredMatch hinj hnodup hi₂ hj₂ hef₂ hx₂ hy₂
  have hsum := gap_sum_of_mirrored (by omega) hii hjj hi₂ hj₂ hs₁ hs₂
  omega

end Gap

end HullSC
end GroupApproximation
