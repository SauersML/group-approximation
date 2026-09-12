import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyComp
import GroupApproximation.GGT.HullSCRelatorSeparation2Locate
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyW4

/-!
# Consecutive letters of a rotation carry opposite indices

The (W4) step reads two ADJACENT components of one piece, and it needs their
indices to be opposite: the first gap of the second match is then in the other
subgroup from the second gap of the first, and `HullSC.eq_one_of_mem_both`
applies.

Inside the run that is `HullSC.blockWord_index_alternates`.  What has to be
added is that reading a rotation does not disturb it.  Two consecutive offsets
of a rotation sit at consecutive positions of the relator UNLESS they straddle
the seam, and the seam is what `0 < |p|` excludes: past the last block letter
comes a BASE letter, so a pair of adjacent letters both of which are blocks
cannot cross it.  That is the whole content, and it is where the base part
earns its keep for the second time --- the first being the wrap argument of
`GGT/HullSCRelatorSeparation2Locate.lean`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Adjacent

variable {G : Type u} [Group G]

/-- **Two consecutive block letters of a rotation carry opposite indices.** -/
theorem index_alternates_of_rotate {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {c d : ℕ} {b b' : Bool} {x x' : G} (hp0 : 0 < p.length)
    (hd : d < (relatorWord₂ p h₀ h₁ ms).length)
    (hd' : d + 1 < (relatorWord₂ p h₀ h₁ ms).length)
    (hx : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (hx' : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b' x')) : b' = !b := by
  have hL : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  obtain ⟨k, hkeq, hklt, hkb⟩ :=
    blockIndex_of_relatorWord₂ (getElem?_of_rotate hd hx)
  obtain ⟨k', hk'eq, hk'lt, hk'b⟩ :=
    blockIndex_of_relatorWord₂ (getElem?_of_rotate hd' hx')
  have hlt1 : 1 < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hstep : (c + (d + 1)) % (relatorWord₂ p h₀ h₁ ms).length
      = (p.length + k + 1) % (relatorWord₂ p h₀ h₁ ms).length := by
    rw [show c + (d + 1) = c + d + 1 from by omega,
      Nat.add_mod (c + d) 1 (relatorWord₂ p h₀ h₁ ms).length, hkeq,
      Nat.mod_eq_of_lt hlt1]
  rw [hk'eq] at hstep
  have hkk : k' = k + 1 := by
    rcases Nat.lt_or_ge (p.length + k + 1)
        (relatorWord₂ p h₀ h₁ ms).length with hcase | hcase
    · rw [Nat.mod_eq_of_lt hcase] at hstep
      omega
    · have heq : p.length + k + 1 = (relatorWord₂ p h₀ h₁ ms).length := by
        omega
      rw [heq, Nat.mod_self] at hstep
      omega
  subst hkk
  exact blockWord_index_alternates h₀ h₁ false ms k b b' x x' hkb hk'b

/-- **Two matches at adjacent components land at adjacent far-side
components.**

The near-side letters at `d` and `d + 1` are consecutive letters of the
relator, and each match pins its far-side letter to the SAME letter --- that is
`HullSC.position_eq_of_alignedMatch`, which needs only the exponents to agree.
So the two far positions are consecutive too, and
`HullSC.farSide_succ_of_positions` reads that off the two congruences.

The far components end at `k₀` and `k₁`, so they START at `k₀ - 1` and
`k₁ - 1`; the conclusion is stated at the ends because that is how
`GGT.OsinComponents.DeepMatchOutput` returns them.  The hypothesis
`k₀ < |R|` is the one boundary: it fails only when the far component is the
last letter of a piece that is the whole rotation, and a caller with two
candidate pairs has it at one of them. -/
theorem farSide_adjacent_of_matches {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' d k₀ k₁ : ℕ} {b₀ b₁ : Bool} {e₀ e₁ : ℕ}
    (hd : d < (relatorWord₂ p h₀ h₁ ms).length)
    (hd' : d + 1 < (relatorWord₂ p h₀ h₁ ms).length)
    (hj₀ : k₀ - 1 < (relatorWord₂ p h₀ h₁ ms).length)
    (hj₁ : k₁ - 1 < (relatorWord₂ p h₀ h₁ ms).length)
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hlt : k₀ < (relatorWord₂ p h₀ h₁ ms).length)
    (hl₀ : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b₀ ((if b₀ then h₁ else h₀) ^ e₀)))
    (hl₁ : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then h₁ else h₀) ^ e₁)))
    (hm₀ : ((relatorWord₂ p h₀ h₁ ms).rotate c')[k₀ - 1]?
      = some (GGT.RelLetter.comp b₀ ((if b₀ then h₁ else h₀) ^ e₀)))
    (hm₁ : ((relatorWord₂ p h₀ h₁ ms).rotate c')[k₁ - 1]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then h₁ else h₀) ^ e₁))) :
    k₁ = k₀ + 1 := by
  have hp₀ := position_eq_of_alignedMatch hinj hnodup hd hj₀ rfl hl₀ hm₀
  have hp₁ := position_eq_of_alignedMatch hinj hnodup hd' hj₁ rfl hl₁ hm₁
  have hstep := farSide_succ_of_positions hp₀ hp₁ (by omega) (by omega)
  omega

/-- **The gap between two adjacent matches is trivial.**

Written against the CONNECTORS the matching step returns rather than the
polygon's gaps, which is what makes it short.  `hc₀` joins the start of the
component at `d` to the vertex `k₀`; `hc₁` joins the start of the next
component to `k₁`.  The element in question,

    T = (Y · vertex 1 u (d+1))⁻¹ · vertex 1 u' k₀,

is `vd⁻¹ * h₀` --- so it lies in `H_{b₀}`, the index of the letter at `d` ---
and it is also `h₁ * vk⁻¹`, so it lies in `H_{b₁}`, the index of the far letter
between `k₀` and `k₁`.  Alternation makes those indices opposite and (W4)
finishes.

No polygon gap is used, and neither is `hpair`: the two connectors and the two
letters' values are the whole input. -/
theorem trivialGap_of_two_connectors {D : GGT.RelGenSet G Bool}
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {b₀ b₁ : Bool} (halt : b₁ = !b₀) {Y h₀ h₁ vd vk : G}
    {u u' : List (GGT.RelLetter G Bool)} {d k₀ k₁ : ℕ}
    (hh₀ : h₀ ∈ D.fam b₀) (hh₁ : h₁ ∈ D.fam b₁)
    (hc₀ : Y * GGT.OsinComponents.vertex (1 : G) u d * h₀
      = GGT.OsinComponents.vertex (1 : G) u' k₀)
    (hc₁ : Y * GGT.OsinComponents.vertex (1 : G) u (d + 1) * h₁
      = GGT.OsinComponents.vertex (1 : G) u' k₁)
    (hvd : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u (d + 1) = vd)
    (hvdm : vd ∈ D.fam b₀)
    (hvk : (GGT.OsinComponents.vertex (1 : G) u' k₀)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' k₁ = vk)
    (hvkm : vk ∈ D.fam b₁) :
    (Y * GGT.OsinComponents.vertex (1 : G) u (d + 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' k₀ = 1 := by
  have hT₀ : (Y * GGT.OsinComponents.vertex (1 : G) u (d + 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' k₀ = vd⁻¹ * h₀ := by
    rw [← hc₀, ← hvd]
    group
  have hT₁ : (Y * GGT.OsinComponents.vertex (1 : G) u (d + 1))⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u' k₀ = h₁ * vk⁻¹ := by
    rw [← hvk, ← hc₁]
    group
  refine eq_one_of_mem_both hdisj (b := b₀) ?_ ?_
  · rw [hT₀]
    exact mul_mem (inv_mem hvdm) hh₀
  · rw [← halt, hT₁]
    exact mul_mem hh₁ (inv_mem hvkm)

/-! ## The mirrored side -/

/-- **The mirrored form of the alternation.**  Easier than the direct one: in
`RelWord.revInv R` the run comes FIRST, so a block position `t` satisfies
`t < |ms|`, and `t + 1 ≤ |ms| < |R|` rules out the wrap without any appeal to
where the base part sits. -/
theorem index_alternates_of_rotate_revInv {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} {c d : ℕ} {b b' : Bool} {x x' : G} (hp0 : 0 < p.length)
    (hd : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hd' : d + 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hx : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (hx' : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b' x')) : b' = !b := by
  have hrev : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = (relatorWord₂ p h₀ h₁ ms).length := RelWord.length_revInv _
  have hL : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  obtain ⟨hklt, hkb⟩ :=
    blockIndex_of_revInv_relatorWord₂ (getElem?_of_rotate hd hx)
  obtain ⟨hk'lt, hk'b⟩ :=
    blockIndex_of_revInv_relatorWord₂ (getElem?_of_rotate hd' hx')
  have hlt1 : 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
    omega
  have hstep : (c + (d + 1))
        % (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = (c + d) % (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length + 1 := by
    rw [show c + (d + 1) = c + d + 1 from by omega,
      Nat.add_mod (c + d) 1 (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length,
      Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt (by omega)]
  rw [hstep] at hk'b hk'lt
  exact revInv_blockWord_index_alternates h₀ h₁ false ms (by omega) hkb hk'b

/-- **The mirrored form of the far-side adjacency.**  The same two congruences,
read through `HullSC.position_eq_of_alignedMatch_revInv`; the letters carry
inverted powers and nothing else changes. -/
theorem farSide_adjacent_of_matches_revInv {p : List G} {h₀ h₁ : G}
    {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' d k₀ k₁ : ℕ} {b₀ b₁ : Bool} {e₀ e₁ : ℕ}
    (hd : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hd' : d + 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hj₀ : k₀ - 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hj₁ : k₁ - 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hlt : k₀ < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hl₀ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b₀ (((if b₀ then h₁ else h₀) ^ e₀)⁻¹)))
    (hl₁ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d + 1]?
      = some (GGT.RelLetter.comp b₁ (((if b₁ then h₁ else h₀) ^ e₁)⁻¹)))
    (hm₀ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[k₀ - 1]?
      = some (GGT.RelLetter.comp b₀ (((if b₀ then h₁ else h₀) ^ e₀)⁻¹)))
    (hm₁ : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[k₁ - 1]?
      = some (GGT.RelLetter.comp b₁ (((if b₁ then h₁ else h₀) ^ e₁)⁻¹))) :
    k₁ = k₀ + 1 := by
  have hp₀ :=
    position_eq_of_alignedMatch_revInv hinj hnodup hd hj₀ rfl hl₀ hm₀
  have hp₁ :=
    position_eq_of_alignedMatch_revInv hinj hnodup hd' hj₁ rfl hl₁ hm₁
  have hstep := farSide_succ_of_positions hp₀ hp₁ (by omega) (by omega)
  omega

end Adjacent

end HullSC
end GroupApproximation
