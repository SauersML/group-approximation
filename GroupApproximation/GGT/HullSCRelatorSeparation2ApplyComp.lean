import GroupApproximation.GGT.HullSCRelatorSeparation2Component
import GroupApproximation.GGT.HullSCRelatorSeparation2Locate

/-!
# A block letter of a matched prefix is a component of it

`HullSC.isComp_relatorWord₂` says each block letter of the alternating relator
is its own maximal component, at position `|p| + i` of the relator itself.  The
polygon is run on a PREFIX of a ROTATION of a member of the symmetrized closure,
and neither passage is free:

* under a rotation the letter before a block letter is the letter before it
  modulo the length, which for the first block letter of the rotation is the
  last letter of the relator, and for the last is the first;
* under truncation to a prefix the clauses only have to be checked below the
  prefix's length, which is what makes the passage possible at all.

Both are done here.

The rotation is where `0 < |p|` is spent, on both sides and for two different
reasons.  In the relator the run comes after the base part, so a wrap-around at
the predecessor would put the block letter at position `0`, which is a base
letter; in the formal inverse the run comes first, so a wrap-around at the
successor would need the letter at `|R| - 1` to be a block letter, and it is a
base letter.  Neither happens, and the neighbours are then the run's own, which
`HullSC.blockWord_index_alternates` --- and, on the mirrored side,
`revInv_blockWord_index_alternates` --- says carry the opposite index.

The prefix passage is `isComp_prefix`, and it needs nothing: the five clauses of
`GGT.OsinComponents.IsComp` all quantify over indices below the word's length,
and below `|pre|` a prefix reads what the word reads.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Read

variable {G : Type u} [Group G]

omit [Group G] in
/-- **A letter carrying an index reads as a component letter of that index.**
The converse of `HullSC.isCompOf_of_getElem?`, which is what turns a clause of
`GGT.OsinComponents.IsComp` back into something the run's arithmetic can
read. -/
theorem getElem?_comp_of_isCompOf {w : List (GGT.RelLetter G Bool)} {j : ℕ}
    (hj : j < w.length) {b : Bool} (hc : (w[j]'hj).IsCompOf b) :
    ∃ y : G, w[j]? = some (GGT.RelLetter.comp b y) := by
  have hget : w[j]? = some (w[j]'hj) := List.getElem?_eq_getElem hj
  cases hw : w[j]'hj with
  | base g =>
      rw [hw] at hc
      exact absurd hc (not_isCompOf_base b g)
  | comp mu y =>
      refine ⟨y, ?_⟩
      have hmu : mu = b := by
        rw [hw] at hc
        exact hc
      rw [hget, hw, hmu]

omit [Group G] in
/-- **A component of a word inside a prefix is a component of the prefix.**
All five clauses restrict, the indices they mention being below the prefix's
length. -/
theorem isComp_prefix {lam : Bool} {pre rest : List (GGT.RelLetter G Bool)}
    {i k : ℕ} (h : GGT.OsinComponents.IsComp lam (pre ++ rest) i k)
    (hk : k ≤ pre.length) :
    GGT.OsinComponents.IsComp lam pre i k := by
  obtain ⟨hik, -, hrange, hpre, hpost⟩ := h
  refine ⟨hik, hk, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hjv
    have hjw : j < (pre ++ rest).length := by
      rw [List.length_append]
      omega
    have hidx : (pre ++ rest)[j]'hjw = pre[j]'hjv := List.getElem_append_left hjv
    rw [← hidx]
    exact hrange j hj1 hj2 hjw
  · intro j hj hjv
    have hjw : j < (pre ++ rest).length := by
      rw [List.length_append]
      omega
    have hidx : (pre ++ rest)[j]'hjw = pre[j]'hjv := List.getElem_append_left hjv
    rw [← hidx]
    exact hpre j hj hjw
  · intro hkv
    have hkw : k < (pre ++ rest).length := by
      rw [List.length_append]
      omega
    have hidx : (pre ++ rest)[k]'hkw = pre[k]'hkv := List.getElem_append_left hkv
    rw [← hidx]
    exact hpost hkw

/-- **Reading a formal inverse at an index, as a letter.**  The letter at the
reversed position carries the same index and the inverse element. -/
theorem getElem?_comp_of_revInv {l : List (GGT.RelLetter G Bool)} {t q : ℕ}
    (hq : t + q + 1 = l.length) {b : Bool} {x : G}
    (hx : (RelWord.revInv l)[t]? = some (GGT.RelLetter.comp b x)) :
    l[q]? = some (GGT.RelLetter.comp b x⁻¹) := by
  rw [getElem?_revInv' hq] at hx
  obtain ⟨d, hd, hfd⟩ := Option.map_eq_some_iff.mp hx
  cases d with
  | base g =>
      have hfd' : (GGT.RelLetter.base g⁻¹ : GGT.RelLetter G Bool)
          = GGT.RelLetter.comp b x := hfd
      exact absurd hfd' (base_ne_comp g⁻¹ x b)
  | comp cc z =>
      have hfd' : (GGT.RelLetter.comp cc z⁻¹ : GGT.RelLetter G Bool)
          = GGT.RelLetter.comp b x := hfd
      rw [GGT.RelLetter.comp.injEq] at hfd'
      obtain ⟨hcb, hzx⟩ := hfd'
      rw [hd, hcb, ← hzx, inv_inv]

/-- **Consecutive letters of the mirrored run carry opposite indices.**
Reversal turns two consecutive positions into two consecutive positions read
backwards, and the run alternates either way round. -/
theorem revInv_blockWord_index_alternates (h₀ h₁ : G) (s : Bool) (ms : List ℕ)
    {t : ℕ} {b b' : Bool} {x x' : G} (ht : t + 1 < ms.length)
    (hb : (RelWord.revInv (blockWord h₀ h₁ s ms))[t]?
      = some (GGT.RelLetter.comp b x))
    (hb' : (RelWord.revInv (blockWord h₀ h₁ s ms))[t + 1]?
      = some (GGT.RelLetter.comp b' x')) : b' = !b := by
  have hlen : (blockWord h₀ h₁ s ms).length = ms.length :=
    length_blockWord h₀ h₁ s ms
  have hq : t + (ms.length - 1 - t) + 1 = (blockWord h₀ h₁ s ms).length := by
    rw [hlen]
    omega
  have hq' : t + 1 + (ms.length - 2 - t) + 1
      = (blockWord h₀ h₁ s ms).length := by
    rw [hlen]
    omega
  have e1 := getElem?_comp_of_revInv hq hb
  have e2 := getElem?_comp_of_revInv hq' hb'
  have hstep : ms.length - 1 - t = ms.length - 2 - t + 1 := by omega
  rw [hstep] at e1
  have halt := blockWord_index_alternates h₀ h₁ s ms (ms.length - 2 - t) b' b
    x'⁻¹ x⁻¹ e2 e1
  rw [halt]
  cases b' with
  | false => rfl
  | true => rfl

end Read

section Rotate

variable {G : Type u} [Group G]

/-- **A block letter of a rotation of the relator is a component of it.**

The letter itself carries the index; the letter before it is a base letter or a
block letter of the opposite index, and so is the letter after it.  A
wrap-around at the predecessor would put the block letter at position `0` of the
relator, which is a base letter, and one at the successor would put a block
letter at position `0`, likewise --- both excluded by `0 < |p|`. -/
theorem isComp_rotate_relatorWord₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hp : 0 < p.length) {c d : ℕ} {b : Bool} {x : G}
    (hd : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    GGT.OsinComponents.IsComp b ((relatorWord₂ p h₀ h₁ ms).rotate c) d
      (d + 1) := by
  have hlenR : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  have hlenW : ((relatorWord₂ p h₀ h₁ ms).rotate c).length
      = (relatorWord₂ p h₀ h₁ ms).length := by
    rw [List.length_rotate]
  obtain ⟨hdW, -⟩ := List.getElem?_eq_some_iff.mp hd
  have hdR : d < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hR := getElem?_of_rotate hdR hd
  obtain ⟨i₀, hpos, hi₀, hbi⟩ := blockIndex_of_relatorWord₂ hR
  have hL : 1 < (relatorWord₂ p h₀ h₁ ms).length := by omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro n _ hn2 hnv
    have hn0 : n = d := by omega
    subst hn0
    exact isCompOf_of_getElem? (b := b) (x := x) hnv hd
  · intro n hn hnv hc
    subst hn
    obtain ⟨y, hy⟩ := getElem?_comp_of_isCompOf hnv hc
    have hnR : n < (relatorWord₂ p h₀ h₁ ms).length := by omega
    have hRn := getElem?_of_rotate hnR hy
    rcases mod_succ_cases c n (relatorWord₂ p h₀ h₁ ms).length hL with
      hcase | ⟨-, hzero⟩
    · obtain ⟨i₁, hpos1, hi₁, hb1⟩ := blockIndex_of_relatorWord₂ hRn
      have hstep : p.length + i₀ = p.length + i₁ + 1 := by
        rw [← hpos, hcase, hpos1]
      have hii : i₀ = i₁ + 1 := by omega
      rw [hii] at hbi
      have halt := blockWord_index_alternates h₀ h₁ false ms i₁ b b y x hb1 hbi
      cases b with
      | false => simp at halt
      | true => simp at halt
    · have h0 : (0 : ℕ) = p.length + i₀ := by
        rw [← hzero]
        exact hpos
      omega
  · intro hk hc
    obtain ⟨y, hy⟩ := getElem?_comp_of_isCompOf hk hc
    have hkR : d + 1 < (relatorWord₂ p h₀ h₁ ms).length := by omega
    have hRk := getElem?_of_rotate hkR hy
    rcases mod_succ_cases c d (relatorWord₂ p h₀ h₁ ms).length hL with
      hcase | ⟨-, hzero⟩
    · obtain ⟨i₂, hpos2, hi₂, hb2⟩ := blockIndex_of_relatorWord₂ hRk
      have hstep : p.length + i₂ = p.length + i₀ + 1 := by
        rw [← hpos2, hcase, hpos]
      have hii : i₂ = i₀ + 1 := by omega
      rw [hii] at hb2
      have halt := blockWord_index_alternates h₀ h₁ false ms i₀ b b x y hbi hb2
      cases b with
      | false => simp at halt
      | true => simp at halt
    · obtain ⟨i₃, hpos3, -, -⟩ := blockIndex_of_relatorWord₂ hRk
      have h0 : (0 : ℕ) = p.length + i₃ := by
        rw [← hzero]
        exact hpos3
      omega

/-- **The mirrored form.**

In the formal inverse the run comes first, so the two wrap-arounds are excluded
for the mirror-image reason: a block letter at the predecessor's position would
put it at `|R| - 1`, which is a base letter, and one at the successor's would
need the position past the run to carry an index. -/
theorem isComp_rotate_revInv_relatorWord₂ {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} (hp : 0 < p.length) {c d : ℕ} {b : Bool} {x : G}
    (hd : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    GGT.OsinComponents.IsComp b
      ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c) d (d + 1) := by
  have hlenM : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = p.length + ms.length := by
    rw [RelWord.length_revInv, length_relatorWord₂]
  have hlenW : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c).length
      = (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
    rw [List.length_rotate]
  obtain ⟨hdW, -⟩ := List.getElem?_eq_some_iff.mp hd
  have hdR : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by omega
  have hR := getElem?_of_rotate hdR hd
  obtain ⟨ht₀, hbi⟩ := blockIndex_of_revInv_relatorWord₂ hR
  have hL : 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro n _ hn2 hnv
    have hn0 : n = d := by omega
    subst hn0
    exact isCompOf_of_getElem? (b := b) (x := x) hnv hd
  · intro n hn hnv hc
    subst hn
    obtain ⟨y, hy⟩ := getElem?_comp_of_isCompOf hnv hc
    have hnR : n < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
      omega
    have hRn := getElem?_of_rotate hnR hy
    rcases mod_succ_cases c n (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      hL with hcase | ⟨hwrap, -⟩
    · obtain ⟨ht₁, hb1⟩ := blockIndex_of_revInv_relatorWord₂ hRn
      rw [hcase] at hbi ht₀
      have halt := revInv_blockWord_index_alternates h₀ h₁ false ms
        (by omega) hb1 hbi
      cases b with
      | false => simp at halt
      | true => simp at halt
    · obtain ⟨ht₁, -⟩ := blockIndex_of_revInv_relatorWord₂ hRn
      omega
  · intro hk hc
    obtain ⟨y, hy⟩ := getElem?_comp_of_isCompOf hk hc
    have hkR : d + 1 < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
      omega
    have hRk := getElem?_of_rotate hkR hy
    rcases mod_succ_cases c d (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      hL with hcase | ⟨hwrap, -⟩
    · obtain ⟨ht₂, hb2⟩ := blockIndex_of_revInv_relatorWord₂ hRk
      rw [hcase] at hb2 ht₂
      have halt := revInv_blockWord_index_alternates h₀ h₁ false ms
        (by omega) hbi hb2
      cases b with
      | false => simp at halt
      | true => simp at halt
    · omega

end Rotate

section Prefix

variable {G : Type u} [Group G]

/-- **A block letter of a matched prefix is a component of the prefix.**
The form the polygon's `IsComp` clause is met in: the long sides of the
quadrilateral are prefixes of two members of the symmetrized closure. -/
theorem isComp_prefix_rotate_relatorWord₂ {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} (hp : 0 < p.length) {c d : ℕ} {b : Bool} {x : G}
    {pre rest : List (GGT.RelLetter G Bool)}
    (hsplit : (relatorWord₂ p h₀ h₁ ms).rotate c = pre ++ rest)
    (hdpre : d < pre.length)
    (hd : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    GGT.OsinComponents.IsComp b pre d (d + 1) := by
  have h := isComp_rotate_relatorWord₂ hp hd
  rw [hsplit] at h
  exact isComp_prefix h (by omega)

/-- **The mirrored form.** -/
theorem isComp_prefix_rotate_revInv_relatorWord₂ {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} (hp : 0 < p.length) {c d : ℕ} {b : Bool} {x : G}
    {pre rest : List (GGT.RelLetter G Bool)}
    (hsplit : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c = pre ++ rest)
    (hdpre : d < pre.length)
    (hd : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    GGT.OsinComponents.IsComp b pre d (d + 1) := by
  have h := isComp_rotate_revInv_relatorWord₂ hp hd
  rw [hsplit] at h
  exact isComp_prefix h (by omega)

end Prefix

end HullSC
end GroupApproximation
