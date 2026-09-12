import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyComp

/-!
# A long piece meets the run

Olshanskii's step (a) is run at a block letter of the matched prefix, so the
first thing the composition owes is that a matched prefix HAS one.  It does, and
for a reason that fixes a design constraint worth stating plainly.

The relator is `|p|` base letters followed by `|ms|` block letters, so in any
rotation the base part is one arc of length `|p|` and the run is the
complementary arc.  A window of more than `|p|` consecutive letters therefore
cannot lie inside the base arc, and meets the run.  In the formal inverse the
two arcs change places and the same count applies.

**The constraint.**  `B` is chosen before the exponent list but after `t`, and
the piece hypothesis is `B < |u₀|`.  For that to put a block letter inside `u₀`
the caller must take `B` at least `|p|`, with `p` a spelling of `t⁻¹` fixed
independently of the length `L` the exponent list is asked for.  A caller that
lengthens `p` with `L` --- which `HullSC.exists_long_base_spelling` invites,
since `0 < |p|` is wanted elsewhere --- can be handed a piece lying wholly
inside the base part, and the argument has nothing to say about it.  So `p` is
chosen once, long enough for `0 < |p|`, and `B` is taken past its length.

The offset is written down rather than found: in the direct relator the first
run position at or after the rotation's start is `max (c mod |R|) |p|`, at
offset `|p| - c mod |R|`, which is at most `|p|`; in the formal inverse it is
`0` or `c mod |R|`, at offset `|R| - c mod |R|` or `0`, again at most `|p|`.
Both are inside a window longer than `|p|`, which is the whole content.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Reading a rotation at an offset -/

/-- **Reading a rotation at an offset**, as an equation rather than an
implication.  `HullSC.getElem?_of_rotate` is this transported along a
hypothesis. -/
theorem getElem?_rotate_eq {α : Type v} {l : List α} {c d : ℕ}
    (hd : d < l.length) : (l.rotate c)[d]? = l[(c + d) % l.length]? := by
  rw [getElem?_rotate_at hd,
    getElem?_rotate_head (Nat.lt_of_le_of_lt (Nat.zero_le d) hd)]

/-! ## The two offsets -/

/-- **A window of more than `P` letters meets the arc `[P, P+M)`**, at an offset
of at most `P`.  The arithmetic behind the direct relator, whose run comes after
its base part. -/
theorem exists_offset_ge (P M c : ℕ) (hM : 0 < M) :
    ∃ d q : ℕ, d ≤ P ∧ d < P + M ∧ P ≤ q ∧ q < P + M ∧
      (c + d) % (P + M) = q := by
  have hL : 0 < P + M := by omega
  have hlt : c % (P + M) < P + M := Nat.mod_lt _ hL
  rcases Nat.lt_or_ge (c % (P + M)) P with hcase | hcase
  · refine ⟨P - c % (P + M), P, by omega, by omega, le_rfl, by omega, ?_⟩
    have hd : P - c % (P + M) < P + M := by omega
    rw [Nat.add_mod c (P - c % (P + M)) (P + M), Nat.mod_eq_of_lt hd,
      show c % (P + M) + (P - c % (P + M)) = P from by omega,
      Nat.mod_eq_of_lt (show P < P + M from by omega)]
  · exact ⟨0, c % (P + M), by omega, by omega, hcase, hlt, by rw [Nat.add_zero]⟩

/-- **A window of more than `P` letters meets the arc `[0, M)`**, at an offset of
at most `P`.  The arithmetic behind the formal inverse, whose run comes
first. -/
theorem exists_offset_lt (P M c : ℕ) (hM : 0 < M) :
    ∃ d q : ℕ, d ≤ P ∧ d < P + M ∧ q < M ∧ (c + d) % (P + M) = q := by
  have hL : 0 < P + M := by omega
  have hlt : c % (P + M) < P + M := Nat.mod_lt _ hL
  rcases Nat.lt_or_ge (c % (P + M)) M with hcase | hcase
  · exact ⟨0, c % (P + M), by omega, by omega, hcase, by rw [Nat.add_zero]⟩
  · refine ⟨P + M - c % (P + M), 0, by omega, by omega, hM, ?_⟩
    have hd : P + M - c % (P + M) < P + M := by omega
    rw [Nat.add_mod c (P + M - c % (P + M)) (P + M), Nat.mod_eq_of_lt hd,
      show c % (P + M) + (P + M - c % (P + M)) = P + M from by omega,
      Nat.mod_self]

/-! ## A long prefix carries a block letter -/

section Block

variable {G : Type u} [Group G]

/-- **A window of more than `|p|` letters of a rotation of the relator carries a
block letter**, with its exponent one of the list's. -/
theorem exists_block_of_long_prefix_rotate {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} (hms : 0 < ms.length) {c n : ℕ} (hn : p.length < n) :
    ∃ (d : ℕ) (b : Bool) (e : ℕ), d < n ∧ e ∈ ms ∧
      ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
        = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ e)) := by
  have hLval : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  obtain ⟨d, q, hdP, hdL, hqP, hqL, hq⟩ :=
    exists_offset_ge p.length ms.length c hms
  obtain ⟨i, hqi⟩ : ∃ i : ℕ, q = p.length + i := ⟨q - p.length, by omega⟩
  subst hqi
  have hdR : d < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hread : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = (relatorWord₂ p h₀ h₁ ms)[p.length + i]? := by
    rw [getElem?_rotate_eq hdR, hLval, hq]
  obtain ⟨b, x, hb⟩ :=
    blockWord_getElem?_comp h₀ h₁ false ms (show i < ms.length from by omega)
  obtain ⟨m, hm, hxm⟩ :=
    blockWord_getElem?_exponent h₀ h₁ false ms i b x hb
  refine ⟨d, b, m, by omega, List.mem_of_getElem? hm, ?_⟩
  rw [hread, relatorWord₂_getElem?_block, hb, hxm]

/-- **The mirrored form.**  In the formal inverse the run comes first, the
letters carry inverses, and the same count applies. -/
theorem exists_block_of_long_prefix_rotate_revInv {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} (hms : 0 < ms.length) {c n : ℕ} (hn : p.length < n) :
    ∃ (d : ℕ) (b : Bool) (e : ℕ), d < n ∧ e ∈ ms ∧
      ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
        = some (GGT.RelLetter.comp b (((if b then h₁ else h₀) ^ e)⁻¹)) := by
  have hLval : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = p.length + ms.length := by
    rw [RelWord.length_revInv, length_relatorWord₂]
  obtain ⟨d, q, hdP, hdL, hqM, hq⟩ := exists_offset_lt p.length ms.length c hms
  have hdR : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by omega
  have hread : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = (RelWord.revInv (relatorWord₂ p h₀ h₁ ms))[q]? := by
    rw [getElem?_rotate_eq hdR, hLval, hq]
  have hbwlen : (RelWord.revInv (blockWord h₀ h₁ false ms)).length
      = ms.length := by
    rw [RelWord.length_revInv, length_blockWord]
  have hsplit : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms))[q]?
      = (RelWord.revInv (blockWord h₀ h₁ false ms))[q]? := by
    rw [revInv_relatorWord₂]
    exact List.getElem?_append_left (by omega)
  obtain ⟨b, z, hbz⟩ := blockWord_getElem?_comp h₀ h₁ false ms
    (show ms.length - 1 - q < ms.length from by omega)
  have hqq : q + (ms.length - 1 - q) + 1 = (blockWord h₀ h₁ false ms).length := by
    rw [length_blockWord]
    omega
  have hrev : (RelWord.revInv (blockWord h₀ h₁ false ms))[q]?
      = some (GGT.RelLetter.comp b z⁻¹) := by
    have h1 := getElem?_revInv' hqq
    rw [hbz] at h1
    exact h1
  obtain ⟨m, hm, hzm⟩ :=
    blockWord_getElem?_exponent h₀ h₁ false ms (ms.length - 1 - q) b z hbz
  refine ⟨d, b, m, by omega, List.mem_of_getElem? hm, ?_⟩
  rw [hread, hsplit, hrev, hzm]

end Block

end HullSC
end GroupApproximation
