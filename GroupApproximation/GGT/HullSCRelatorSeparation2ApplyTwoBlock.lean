import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyBlock

/-!
# Two block letters in one piece, far apart

The mixed cases of the dispatch run Olshanskii's step (a) twice inside the same
piece and compare the two matches, so what they ask of the piece is not one
block letter but two, at offsets more than the pinning separation apart.

`HullSC.exists_block_of_long_prefix_rotate` produces one, at an offset of at
most `|p|`, and produces it by writing the offset down rather than by finding
it.  Two are produced the same way.  A window of `|p| + k + 2` consecutive
letters of a rotation always contains two run positions more than `k` apart:
if the window starts in the base arc, the run begins at an offset of at most
`|p|` and the next `k + 1` run letters follow it inside the window; if it
starts inside the run, either the run's remaining tail holds both, or the tail
is shorter than `k + 1`, and then the window reaches past the base arc into the
run again at an offset that the tail's shortness bounds by `|p| + k + 1`.

**The two constants this earns.**  The threshold is `|p| + k + 2`, with `k` the
separation the pinning argument asks for; that is the value `B` is given in the
construction.  The second offset is at most `|p| + k + 1`, which is what the
mixed closers' length hypothesis is discharged from: `d₂ - d₁ ≤ |p| + k + 1`,
so an exponent list longer than `|p| + 5k + 2` leaves room for
`2 (d₂ - d₁) + 3k` inside the relator.  Both bounds are conclusions here rather
than recomputations at the call sites.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Reading a sum modulo the length -/

/-- **A sum that does not wrap.**  The offset is small enough that the reading
position is the residue plus the offset. -/
theorem add_mod_of_sum_eq {c d L s : ℕ} (h : c % L + d = s) (hs : s < L) :
    (c + d) % L = s := by
  have hd : d < L := by omega
  rw [Nat.add_mod c d L, Nat.mod_eq_of_lt hd, h, Nat.mod_eq_of_lt hs]

/-- **A sum that wraps once.**  The offset carries the reading position past
the end of the word exactly once. -/
theorem add_mod_of_sum_eq_wrap {c d L s : ℕ} (hd : d < L)
    (h : c % L + d = L + s) (hs : s < L) : (c + d) % L = s := by
  rw [Nat.add_mod c d L, Nat.mod_eq_of_lt hd, h, Nat.add_mod_left,
    Nat.mod_eq_of_lt hs]

/-! ## The two pairs of offsets -/

/-- **Two offsets into the arc `[P, P + M)`**, more than `k` apart, the second
at most `P + k + 1`.  The arithmetic behind the direct relator, whose run comes
after its base part. -/
theorem exists_two_offsets_ge (P M c k : ℕ) (hM : k + 2 ≤ M) :
    ∃ d₁ d₂ q₁ q₂ : ℕ, d₁ + k < d₂ ∧ d₂ ≤ P + k + 1 ∧
      P ≤ q₁ ∧ q₁ < P + M ∧ P ≤ q₂ ∧ q₂ < P + M ∧
      (c + d₁) % (P + M) = q₁ ∧ (c + d₂) % (P + M) = q₂ := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, c % (P + M) = r := ⟨_, rfl⟩
  have hlt : r < P + M := by
    rw [← hr]
    exact Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge r P with hcase | hcase
  · refine ⟨P - r, P - r + (k + 1), P, P + k + 1, by omega, by omega, by omega,
      by omega, by omega, by omega, ?_, ?_⟩
    · exact add_mod_of_sum_eq (by omega) (by omega)
    · exact add_mod_of_sum_eq (by omega) (by omega)
  rcases Nat.lt_or_ge (r + k + 1) (P + M) with hcase2 | hcase2
  · refine ⟨0, k + 1, r, r + k + 1, by omega, by omega, hcase, hlt, by omega,
      by omega, ?_, ?_⟩
    · exact add_mod_of_sum_eq (by omega) (by omega)
    · exact add_mod_of_sum_eq (by omega) (by omega)
  · refine ⟨0, P + M - r + P + (k + 1 - (P + M - r + P)), r,
      P + (k + 1 - (P + M - r + P)), by omega, by omega, hcase, hlt, by omega,
      by omega, ?_, ?_⟩
    · exact add_mod_of_sum_eq (by omega) (by omega)
    · exact add_mod_of_sum_eq_wrap (by omega) (by omega) (by omega)

/-- **Two offsets into the arc `[0, M)`**, more than `k` apart, the second at
most `P + k + 1`.  The arithmetic behind the formal inverse, whose run comes
first. -/
theorem exists_two_offsets_lt (P M c k : ℕ) (hM : k + 2 ≤ M) :
    ∃ d₁ d₂ q₁ q₂ : ℕ, d₁ + k < d₂ ∧ d₂ ≤ P + k + 1 ∧
      q₁ < M ∧ q₂ < M ∧
      (c + d₁) % (P + M) = q₁ ∧ (c + d₂) % (P + M) = q₂ := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, c % (P + M) = r := ⟨_, rfl⟩
  have hlt : r < P + M := by
    rw [← hr]
    exact Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge r M with hcase | hcase
  · rcases Nat.lt_or_ge (r + k + 1) M with hcase2 | hcase2
    · refine ⟨0, k + 1, r, r + k + 1, by omega, by omega, hcase, by omega, ?_,
        ?_⟩
      · exact add_mod_of_sum_eq (by omega) (by omega)
      · exact add_mod_of_sum_eq (by omega) (by omega)
    · refine ⟨0, P + M - r + (k + 1 - (P + M - r)), r,
        k + 1 - (P + M - r), by omega, by omega, hcase, by omega, ?_, ?_⟩
      · exact add_mod_of_sum_eq (by omega) (by omega)
      · exact add_mod_of_sum_eq_wrap (by omega) (by omega) (by omega)
  · refine ⟨P + M - r, P + M - r + (k + 1), 0, k + 1, by omega, by omega,
      by omega, by omega, ?_, ?_⟩
    · exact add_mod_of_sum_eq_wrap (by omega) (by omega) (by omega)
    · exact add_mod_of_sum_eq_wrap (by omega) (by omega) (by omega)

/-! ## A letter at an offset -/

section Block

variable {G : Type u} [Group G]

/-- **An offset landing in the run of the direct relator carries a block
letter**, with its exponent one of the list's. -/
theorem block_of_offset_ge (h₀ h₁ : G) {p : List G} {ms : List ℕ} {c d i : ℕ}
    (hi : i < ms.length) (hd : d < p.length + ms.length)
    (hq : (c + d) % (p.length + ms.length) = p.length + i) :
    ∃ (b : Bool) (e : ℕ), e ∈ ms ∧
      ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
        = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ e)) := by
  have hLval : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  have hdR : d < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hread : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = (relatorWord₂ p h₀ h₁ ms)[p.length + i]? := by
    rw [getElem?_rotate_eq hdR, hLval, hq]
  obtain ⟨b, x, hb⟩ := blockWord_getElem?_comp h₀ h₁ false ms hi
  obtain ⟨m, hm, hxm⟩ := blockWord_getElem?_exponent h₀ h₁ false ms i b x hb
  exact ⟨b, m, List.mem_of_getElem? hm,
    by rw [hread, relatorWord₂_getElem?_block, hb, hxm]⟩

/-- **An offset landing in the run of the formal inverse carries an inverted
block letter**, with its exponent one of the list's. -/
theorem block_of_offset_lt (h₀ h₁ : G) {p : List G} {ms : List ℕ} {c d q : ℕ}
    (hq0 : q < ms.length) (hd : d < p.length + ms.length)
    (hq : (c + d) % (p.length + ms.length) = q) :
    ∃ (b : Bool) (e : ℕ), e ∈ ms ∧
      ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
        = some (GGT.RelLetter.comp b (((if b then h₁ else h₀) ^ e)⁻¹)) := by
  have hLval : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = p.length + ms.length := by
    rw [RelWord.length_revInv, length_relatorWord₂]
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
  have hqq : q + (ms.length - 1 - q) + 1
      = (blockWord h₀ h₁ false ms).length := by
    rw [length_blockWord]
    omega
  have hrev : (RelWord.revInv (blockWord h₀ h₁ false ms))[q]?
      = some (GGT.RelLetter.comp b z⁻¹) := by
    have h1 := getElem?_revInv' hqq
    rw [hbz] at h1
    exact h1
  obtain ⟨m, hm, hzm⟩ :=
    blockWord_getElem?_exponent h₀ h₁ false ms (ms.length - 1 - q) b z hbz
  exact ⟨b, m, List.mem_of_getElem? hm, by rw [hread, hsplit, hrev, hzm]⟩

/-! ## Two block letters in a long prefix -/

/-- **A window of `|p| + k + 2` letters of a rotation of the relator carries
two block letters more than `k` apart**, the second at an offset of at most
`|p| + k + 1`. -/
theorem exists_two_blocks_of_long_prefix_rotate {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} {c n k : ℕ} (hms : k + 2 ≤ ms.length)
    (hn : p.length + k + 1 < n) :
    ∃ (d₁ d₂ : ℕ) (b₁ b₂ : Bool) (e₁ e₂ : ℕ),
      d₁ + k < d₂ ∧ d₂ < n ∧ d₂ ≤ p.length + k + 1 ∧
        e₁ ∈ ms ∧ e₂ ∈ ms ∧
      ((relatorWord₂ p h₀ h₁ ms).rotate c)[d₁]?
          = some (GGT.RelLetter.comp b₁ ((if b₁ then h₁ else h₀) ^ e₁)) ∧
      ((relatorWord₂ p h₀ h₁ ms).rotate c)[d₂]?
          = some (GGT.RelLetter.comp b₂ ((if b₂ then h₁ else h₀) ^ e₂)) := by
  obtain ⟨d₁, d₂, q₁, q₂, hsep, hd₂P, hq₁P, hq₁L, hq₂P, hq₂L,
      hmod₁, hmod₂⟩ :=
    exists_two_offsets_ge p.length ms.length c k hms
  obtain ⟨i₁, hi₁⟩ : ∃ i : ℕ, q₁ = p.length + i := ⟨q₁ - p.length, by omega⟩
  obtain ⟨i₂, hi₂⟩ : ∃ i : ℕ, q₂ = p.length + i := ⟨q₂ - p.length, by omega⟩
  subst hi₁
  subst hi₂
  obtain ⟨b₁, e₁, he₁, hb₁⟩ := block_of_offset_ge h₀ h₁
    (show i₁ < ms.length from by omega)
    (show d₁ < p.length + ms.length from by omega) hmod₁
  obtain ⟨b₂, e₂, he₂, hb₂⟩ := block_of_offset_ge h₀ h₁
    (show i₂ < ms.length from by omega)
    (show d₂ < p.length + ms.length from by omega) hmod₂
  exact ⟨d₁, d₂, b₁, b₂, e₁, e₂, hsep, by omega, hd₂P, he₁, he₂, hb₁,
    hb₂⟩

/-- **The mirrored form.**  In the formal inverse the run comes first and the
letters carry inverses; the same count applies. -/
theorem exists_two_blocks_of_long_prefix_rotate_revInv {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} {c n k : ℕ} (hms : k + 2 ≤ ms.length)
    (hn : p.length + k + 1 < n) :
    ∃ (d₁ d₂ : ℕ) (b₁ b₂ : Bool) (e₁ e₂ : ℕ),
      d₁ + k < d₂ ∧ d₂ < n ∧ d₂ ≤ p.length + k + 1 ∧
        e₁ ∈ ms ∧ e₂ ∈ ms ∧
      ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d₁]?
          = some (GGT.RelLetter.comp b₁ (((if b₁ then h₁ else h₀) ^ e₁)⁻¹)) ∧
      ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d₂]?
          = some (GGT.RelLetter.comp b₂ (((if b₂ then h₁ else h₀) ^ e₂)⁻¹)) := by
  obtain ⟨d₁, d₂, q₁, q₂, hsep, hd₂P, hq₁, hq₂, hmod₁, hmod₂⟩ :=
    exists_two_offsets_lt p.length ms.length c k hms
  obtain ⟨b₁, e₁, he₁, hb₁⟩ := block_of_offset_lt h₀ h₁ hq₁
    (show d₁ < p.length + ms.length from by omega) hmod₁
  obtain ⟨b₂, e₂, he₂, hb₂⟩ := block_of_offset_lt h₀ h₁ hq₂
    (show d₂ < p.length + ms.length from by omega) hmod₂
  exact ⟨d₁, d₂, b₁, b₂, e₁, e₂, hsep, by omega, hd₂P, he₁, he₂, hb₁,
    hb₂⟩

end Block

end HullSC
end GroupApproximation
