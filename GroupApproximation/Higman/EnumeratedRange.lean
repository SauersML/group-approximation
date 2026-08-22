import GroupApproximation.Higman.TheoremThreeAssembly

/-!
# Half-line block conditions, and the device that makes a window unique

`Higman.EnumeratedRangeGenerated` (`Higman/TheoremThreeAssembly.lean`) is the
residue of Higman's Theorem 3: the family built from `Z` and `S` is closed under
unions indexed by a total computable enumeration.  The route to it runs a
computation along the index line --- a set of *traces* in blocks of width `m`,
cut out by `Seq.transitionSet`, projected onto its first track by `θᵗ`.

That route has one structural obstruction, and this module removes it.

## The obstruction

A trace encodes one member `g_r` of the enumeration in a finite window of
blocks, with a counter track pinned so that the counter reads the block index.
The transition relation is a condition on *adjacent* blocks, so it cannot see
how many windows a trace has: a second window elsewhere on the line, carrying a
different parameter and a counter offset from the block index, satisfies every
adjacent-block condition and contributes garbage to the value track.  No local
rule forbids it, and no global rule is available --- a track that is nonzero on
a whole half-line is not finitely supported, so it is not a sequence.

## The removal

A *marker* track carrying `1` at the left end of each window is maintained by
the transition relation, and is one entry per window.  So "one window" is "the
marker track vanishes off the origin", which is a condition on all blocks at
once, and this module shows it is generated.

The tool is that an `ω`-condition can be imposed on one half-line only.  `π` is
agreement on the coordinates `i ≤ 0` and `ρ π ρ` is agreement on `0 ≤ i`
(`Seq.rhoOp_piOp_rhoOp`); conjugating `π` by `σ` gives agreement on `i ≤ -1`
(`Seq.sigmaInvOp_piOp_sigmaOp`), which is the threshold a block decomposition
wants.  Applied to `ωₘ B` each of these localizes it, *provided the zero
sequence lies in `B`*: the extension witnessing the agreement is then the
truncation of `f`, padded with zeros, and the padded blocks are the zero block.
That hypothesis is not a technicality --- without it the localizations are
false, since a set `B` avoiding `0` makes `ωₘ B` empty while the half-line
conditions are not.

With both half-lines available, `Seq.trackOffZero` --- the sequences whose
offset-`d` track vanishes on every block but the one at the origin --- is the
intersection of a `σᵐ`-shifted non-negative condition with a negative one, and
is generated.  That is the marker condition, and it is what the trace assembly
was missing.

## What is still owed

The trace assembly itself: the transition relation `A` between adjacent blocks,
which is a recursively enumerable relation of bounded arity, and the correctness
proof identifying the `θᵗ` projection of the trace set with the range.  The
first is the arithmetic of Higman's Section 2 and is untouched here; the second
is bookkeeping over the block calculus below.  `EnumeratedRangeGenerated` is
still the interface and nothing in this module inhabits it.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## 1.  The inverse shift, and agreement below `-1` -/

/-- `σ⁻¹`, as a composite of the operations: `ρ σ ρ`. -/
noncomputable def sigmaInvOp (B : Set E) : Set E := rhoOp (sigmaOp (rhoOp B))

theorem mem_sigmaOp_iff (B : Set E) (f : E) :
    f ∈ sigmaOp B ↔ ∃ g ∈ B, ∀ i : ℤ, f i = g (i - 1) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun i => shiftSeq_apply g i⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, Finsupp.ext fun i => ?_⟩
    rw [shiftSeq_apply]
    exact (h i).symm

theorem mem_sigmaInvOp_iff (B : Set E) (f : E) :
    f ∈ sigmaInvOp B ↔ ∃ g ∈ B, ∀ i : ℤ, f i = g (i + 1) := by
  unfold sigmaInvOp
  constructor
  · rintro ⟨h, hh, hfh⟩
    rw [mem_sigmaOp_iff] at hh
    obtain ⟨k, hk, hhk⟩ := hh
    obtain ⟨g, hg, hkg⟩ := hk
    refine ⟨g, hg, fun i => ?_⟩
    rw [hfh i, hhk (-i), hkg (-i - 1)]
    congr 1
    ring
  · rintro ⟨g, hg, hfg⟩
    refine ⟨reflect f, ?_, ?_⟩
    · rw [mem_sigmaOp_iff]
      refine ⟨reflect g, ⟨g, hg, fun i => reflect_apply g i⟩, fun i => ?_⟩
      rw [reflect_apply, reflect_apply, hfg (-i)]
      congr 1
      ring
    · intro i
      rw [reflect_apply, neg_neg]

theorem higmanGenerated_sigmaInvOp {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (sigmaInvOp B) :=
  HigmanGenerated.rho (HigmanGenerated.sigma (HigmanGenerated.rho h))

/-- **Agreement on the coordinates `i ≤ -1`.**  `π` conjugated by the shift.
This is the threshold a decomposition into blocks wants, since the block at the
origin starts at the coordinate `0`. -/
theorem sigmaInvOp_piOp_sigmaOp (B : Set E) :
    sigmaInvOp (piOp (sigmaOp B)) = Agree.agreeOp (fun i : ℤ => i ≤ -1) B := by
  ext f
  rw [mem_sigmaInvOp_iff]
  constructor
  · rintro ⟨h, ⟨k, hk, hhk⟩, hfh⟩
    rw [mem_sigmaOp_iff] at hk
    obtain ⟨g, hg, hkg⟩ := hk
    refine ⟨g, hg, fun i hi => ?_⟩
    have hi' : i ≤ -1 := hi
    rw [hfh i, hhk (i + 1) (by omega), hkg (i + 1)]
    congr 1
    ring
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, i ≤ -1 → f i = g i := hfg
    refine ⟨shiftSeq f, ?_, fun i => ?_⟩
    · refine ⟨shiftSeq g, ?_, ?_⟩
      · rw [mem_sigmaOp_iff]
        exact ⟨g, hg, fun i => shiftSeq_apply g i⟩
      · intro i hi
        rw [shiftSeq_apply, shiftSeq_apply]
        exact hfg' (i - 1) (by omega)
    · rw [shiftSeq_apply]
      congr 1
      ring

theorem higmanGenerated_agreeOp_le_neg_one {B : Set E} (h : HigmanGenerated B) :
    HigmanGenerated (Agree.agreeOp (fun i : ℤ => i ≤ -1) B) := by
  rw [← sigmaInvOp_piOp_sigmaOp]
  exact higmanGenerated_sigmaInvOp (HigmanGenerated.pi (HigmanGenerated.sigma h))

/-! ## 2.  The block calculus -/

theorem blockAt_apply (m : ℕ) (i j : ℤ) (f : E) :
    blockAt m i f j =
      if j ∈ Finset.Ico (0 : ℤ) (m : ℤ) then f (m * i + j) else 0 := by
  simp only [blockAt, Finsupp.onFinset_apply]

theorem blockAt_apply_of_mem (m : ℕ) (i j : ℤ) (f : E)
    (hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)) : blockAt m i f j = f (m * i + j) := by
  rw [blockAt_apply, if_pos hj]

theorem blockAt_congr (m : ℕ) (i : ℤ) (f g : E)
    (h : ∀ j : ℤ, 0 ≤ j → j < (m : ℤ) → f (m * i + j) = g (m * i + j)) :
    blockAt m i f = blockAt m i g := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj, if_pos hj]
    rw [Finset.mem_Ico] at hj
    exact h j hj.1 hj.2
  · rw [if_neg hj, if_neg hj]

theorem blockAt_eq_zero (m : ℕ) (i : ℤ) (f : E)
    (h : ∀ j : ℤ, 0 ≤ j → j < (m : ℤ) → f (m * i + j) = 0) : blockAt m i f = 0 := by
  refine Finsupp.ext fun j => ?_
  have hz : (0 : E) j = 0 := by simp
  rw [hz, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    rw [Finset.mem_Ico] at hj
    exact h j hj.1 hj.2
  · rw [if_neg hj]

/-- A block at a non-negative index lives in the non-negative coordinates. -/
theorem block_coord_nonneg {m : ℕ} {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) :
    0 ≤ (m : ℤ) * i + j :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg m) hi) hj

/-- A block at a negative index lives in the negative coordinates. -/
theorem block_coord_neg {m : ℕ} {i j : ℤ} (hi : i ≤ -1) (hj : j < (m : ℤ)) :
    (m : ℤ) * i + j ≤ -1 := by
  have h1 : (m : ℤ) * i ≤ (m : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg m)
  omega

/-- Blocks under a shift by a whole block. -/
theorem blockAt_of_shift (m : ℕ) (i : ℤ) (f g : E)
    (h : ∀ i : ℤ, f i = g (i - m)) : blockAt m i f = blockAt m (i - 1) g := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj, if_pos hj, h]
    congr 1
    ring
  · rw [if_neg hj, if_neg hj]

/-! ## 3.  `ω` on one half-line -/

/-- The sequences whose blocks at non-negative indices lie in `B`. -/
def omegaGE (m : ℕ) (B : Set E) : Set E := {f : E | ∀ i : ℤ, 0 ≤ i → blockAt m i f ∈ B}

/-- The sequences whose blocks at negative indices lie in `B`. -/
def omegaLT (m : ℕ) (B : Set E) : Set E := {f : E | ∀ i : ℤ, i ≤ -1 → blockAt m i f ∈ B}

/-- **`ωₘ` localized to the non-negative blocks.**  The zero sequence has to lie
in `B`, because the witness for the agreement is `f` padded with zeros and the
padding is read as the zero block. -/
theorem agreeOp_nonneg_omegaOp (m : ℕ) (B : Set E) (hB : (0 : E) ∈ B) :
    Agree.agreeOp (fun i : ℤ => 0 ≤ i) (omegaOp m B) = omegaGE m B := by
  ext f
  constructor
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, 0 ≤ i → f i = g i := hfg
    intro i hi
    have hb : blockAt m i f = blockAt m i g :=
      blockAt_congr m i f g fun j hj0 _ =>
        hfg' ((m : ℤ) * i + j) (block_coord_nonneg hi hj0)
    rw [hb]
    exact hg i
  · intro hf
    have hf' : ∀ i : ℤ, 0 ≤ i → blockAt m i f ∈ B := hf
    refine ⟨Finsupp.filter (fun j : ℤ => (0 : ℤ) ≤ j) f, ?_, ?_⟩
    · intro i
      by_cases hi : 0 ≤ i
      · have hb : blockAt m i (Finsupp.filter (fun j : ℤ => (0 : ℤ) ≤ j) f)
            = blockAt m i f := by
          refine blockAt_congr m i _ f fun j hj0 _ => ?_
          have hpos : (0 : ℤ) ≤ (m : ℤ) * i + j := block_coord_nonneg hi hj0
          rw [Finsupp.filter_apply, if_pos hpos]
        rw [hb]
        exact hf' i hi
      · have hb : blockAt m i (Finsupp.filter (fun j : ℤ => (0 : ℤ) ≤ j) f) = 0 := by
          refine blockAt_eq_zero m i _ fun j _ hjm => ?_
          have hneg : (m : ℤ) * i + j ≤ -1 := block_coord_neg (by omega) hjm
          rw [Finsupp.filter_apply, if_neg (by omega)]
        rw [hb]
        exact hB
    · intro i hi
      have hi' : (0 : ℤ) ≤ i := hi
      rw [Finsupp.filter_apply, if_pos hi']

/-- **`ωₘ` localized to the negative blocks.** -/
theorem agreeOp_le_neg_one_omegaOp (m : ℕ) (B : Set E) (hB : (0 : E) ∈ B) :
    Agree.agreeOp (fun i : ℤ => i ≤ -1) (omegaOp m B) = omegaLT m B := by
  ext f
  constructor
  · rintro ⟨g, hg, hfg⟩
    have hfg' : ∀ i : ℤ, i ≤ -1 → f i = g i := hfg
    intro i hi
    have hb : blockAt m i f = blockAt m i g :=
      blockAt_congr m i f g fun j _ hjm =>
        hfg' ((m : ℤ) * i + j) (block_coord_neg hi hjm)
    rw [hb]
    exact hg i
  · intro hf
    have hf' : ∀ i : ℤ, i ≤ -1 → blockAt m i f ∈ B := hf
    refine ⟨Finsupp.filter (fun j : ℤ => j ≤ -1) f, ?_, ?_⟩
    · intro i
      by_cases hi : i ≤ -1
      · have hb : blockAt m i (Finsupp.filter (fun j : ℤ => j ≤ -1) f)
            = blockAt m i f := by
          refine blockAt_congr m i _ f fun j _ hjm => ?_
          have hneg : (m : ℤ) * i + j ≤ -1 := block_coord_neg hi hjm
          rw [Finsupp.filter_apply, if_pos hneg]
        rw [hb]
        exact hf' i hi
      · have hb : blockAt m i (Finsupp.filter (fun j : ℤ => j ≤ -1) f) = 0 := by
          refine blockAt_eq_zero m i _ fun j hj0 _ => ?_
          have hpos : (0 : ℤ) ≤ (m : ℤ) * i + j := block_coord_nonneg (by omega) hj0
          rw [Finsupp.filter_apply, if_neg (by omega)]
        rw [hb]
        exact hB
    · intro i hi
      have hi' : i ≤ -1 := hi
      rw [Finsupp.filter_apply, if_pos hi']

theorem higmanGenerated_omegaGE (m : ℕ) (hm : 0 < m) {B : Set E} (hB : (0 : E) ∈ B)
    (h : HigmanGenerated B) : HigmanGenerated (omegaGE m B) := by
  rw [← agreeOp_nonneg_omegaOp m B hB]
  exact higmanGenerated_agreeOp_nonneg (HigmanGenerated.omega m hm h)

theorem higmanGenerated_omegaLT (m : ℕ) (hm : 0 < m) {B : Set E} (hB : (0 : E) ∈ B)
    (h : HigmanGenerated B) : HigmanGenerated (omegaLT m B) := by
  rw [← agreeOp_le_neg_one_omegaOp m B hB]
  exact higmanGenerated_agreeOp_le_neg_one (HigmanGenerated.omega m hm h)

/-! ## 4.  Moving the half-line by one block -/

/-- `σᵐ` shifts the block decomposition by one block, so it turns the
non-negative half-line condition into the strictly positive one. -/
theorem sigmaOp_iterate_omegaGE (m : ℕ) (B : Set E) :
    sigmaOp^[m] (omegaGE m B) = {f : E | ∀ i : ℤ, 1 ≤ i → blockAt m i f ∈ B} := by
  ext f
  rw [mem_sigmaOp_iterate_iff]
  constructor
  · rintro ⟨g, hg, h⟩ i hi
    rw [blockAt_of_shift m i f g h]
    exact hg (i - 1) (by omega)
  · intro hf
    have hf' : ∀ i : ℤ, 1 ≤ i → blockAt m i f ∈ B := hf
    obtain ⟨g, rfl⟩ := exists_shiftSeq_iterate m f
    refine ⟨g, ?_, fun i => shiftSeq_iterate_apply m g i⟩
    intro i hi
    have hb := blockAt_of_shift m (i + 1) (shiftSeq^[m] g) g
      (fun j => shiftSeq_iterate_apply m g j)
    have hii : i + 1 - 1 = i := by ring
    rw [hii] at hb
    rw [← hb]
    exact hf' (i + 1) (by omega)

/-! ## 5.  The marker condition -/

/-- The sequences whose track at the block offset `d` vanishes on every block
except the one at the origin. -/
def trackOffZero (m : ℕ) (d : ℤ) : Set E := {f : E | ∀ i : ℤ, i ≠ 0 → f (m * i + d) = 0}

theorem trackOffZero_eq (m : ℕ) (d : ℤ) (hd0 : 0 ≤ d) (hdm : d < (m : ℤ)) :
    trackOffZero m d
      = sigmaOp^[m] (omegaGE m (pinAt d 0)) ∩ omegaLT m (pinAt d 0) := by
  have hmem : ∀ (i : ℤ) (f : E), blockAt m i f ∈ pinAt d 0 ↔ f (m * i + d) = 0 := by
    intro i f
    have happ : blockAt m i f d = f (m * i + d) :=
      blockAt_apply_of_mem m i d f (Finset.mem_Ico.mpr ⟨hd0, hdm⟩)
    constructor
    · intro h
      have h' : blockAt m i f d = 0 := h
      rwa [happ] at h'
    · intro h
      show blockAt m i f d = 0
      rwa [happ]
  rw [sigmaOp_iterate_omegaGE]
  ext f
  constructor
  · intro hf
    have hf' : ∀ i : ℤ, i ≠ 0 → f (m * i + d) = 0 := hf
    exact ⟨fun i hi => (hmem i f).mpr (hf' i (by omega)),
      fun i hi => (hmem i f).mpr (hf' i (by omega))⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_trichotomy i 0 with h | h | h
    · exact (hmem i f).mp (h2 i (by omega))
    · exact absurd h hi
    · exact (hmem i f).mp (h1 i (by omega))

/-- **The marker condition is generated.**  A track that carries one entry per
window vanishes off the origin exactly when the trace has one window, and that
is a condition the nine operations can impose. -/
theorem higmanGenerated_trackOffZero (m : ℕ) (d : ℤ) (hd0 : 0 ≤ d)
    (hdm : d < (m : ℤ)) : HigmanGenerated (trackOffZero m d) := by
  have hm : 0 < m := by omega
  have h0 : (0 : E) ∈ pinAt d 0 := by
    show (0 : E) d = 0
    simp
  rw [trackOffZero_eq m d hd0 hdm]
  refine HigmanGenerated.inter ?_
    (higmanGenerated_omegaLT m hm h0 (higmanGenerated_pinAt d 0))
  exact higmanGenerated_sigmaOp_iterate m
    (higmanGenerated_omegaGE m hm h0 (higmanGenerated_pinAt d 0))

end Seq
end Higman
end GroupApproximation
