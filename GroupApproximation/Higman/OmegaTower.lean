import GroupApproximation.Higman.OmegaClosure

/-!
# The tower that discharges `ωₘ`, and the half of it that is proved here

`Higman.OmegaClosure` leaves one residue, `Omega.OmegaInput`: benignness of
`A_{ωₘ B}` when `0 ∈ B`.  Its header records why the obvious construction --- a
single HNN extension `F₃ ∗_{shiftAut^m} t` --- cannot discharge it: that
extension computes a *union* over the shift orbit, and `ωₘ` is an
*intersection*.  The route that does work is the three-stage tower of the
modern write-up (Mikaelian, arXiv:1908.10153v8, §4, the last part of Theorem
4.4), and this file is the sequence-side half of it, proved, together with the
interface the group-side half has to supply.

## The tower, and what it is for

Write `ℰ_m` for the sequences supported on the window `[0, m)` --- the possible
`m`-blocks --- and `b_l = ∏ᵢ bᵢ^{l i}` (ascending), `a_l = a^{b_l}` as usual.
The tower is

* `Σ = ⟨b, c⟩ ∗_{B₀ₘ} (g, h, k)`: three new free generators `g, h, k`, each
  *centralizing* `B₀ₘ = ⟨bᵢ : i ∉ [0, m)⟩`, the rows outside the window.  This
  is what makes `g_β` --- the analogue of `a_β` built from `g, h, k` instead of
  `a, b, c` --- commute with `b_l` for every `l` supported off the window.
* `Π = Σ ∗_L a`: the generator `a` re-entered as a stable letter *centralizing*
  `L = ⟨g_β b_β⁻¹ : β ∈ ℰ_m⟩`.  Centralizing `L` is exactly the statement
  `a^{g_β} = a^{b_β} = a_β` for every block `β`.
* `Ω = Π ∗_ρ r`: a stable letter `r` conjugating `F₃` by `ρ = shiftAut^m`, the
  `m`-shift `a, b, c ↦ a, b^{c^m}, c`.  (Mikaelian's `ω`-paragraph calls this
  automorphism `ρ`; it is *not* the reversal that his §4 calls `ρ` elsewhere.
  See `research/mikaelian-rho-tau-shortcuts-fail.md`.)

and the subgroup he calls `W_B = ⟨g_β, a, r | β ∈ B⟩`, with the computation
`F₃ ∩ W_B = A_{ωₘ B}`.

## What is proved here

`Tower m` below is that data in the only form the computation uses: an
injective `emb : F₃ →* G`, elements `gen β` and `stable`, and **three
relations**, which are exactly the three bullets above:

* `conj_stable` --- `stable` conjugates `emb` by `shiftAut^m`;
* `conj_gen` --- `(gen β)⁻¹ · a · gen β = a_β` for `β ∈ ℰ_m`;
* `commute_row` --- `gen β` commutes with the rows outside the window.

Given a tower, the **easy half of the computation is proved in full**:

    ASub_omegaOp_le : A_{ωₘ B} ≤ (W T B).comap emb .

That is `emb_aElt_mem_W`, and it is not a formality.  It is the induction
Mikaelian runs on his worked example: peel the block at index `0` off `l` with
`conj_gen` (legal because `gen β` commutes with the rest of `b_l`, which is
supported off the window --- `commute_gen_bElt`), push the remaining tail down
by one block with `conj_stable`, and recurse.  The bookkeeping that makes it an
induction --- that the tail, unshifted, has one fewer block and still has all
its blocks in `B` (this is where `0 ∈ B` is spent, on the blocks the unshift
vacates) --- is §§2--4 below.

## What is owed

`TowerClosure` names the two remaining obligations, and nothing here inhabits
it:

* `benign` --- `W_B` is benign with a torsion-free witness.  This is where the
  tower has to be *built*, over the benign witness for `A_B` rather than over
  `⟨b, c⟩` itself, and where finite presentation and torsion-freeness are
  discharged: every stage is an HNN extension, so
  `HNNBritton.isPowerTorsionFree_hnn` and `Algebra/HNNFinitePresentation`
  apply, and for any amalgamated stage
  `Algebra/PushoutITorsionFree.isPowerTorsionFree_pushoutI_of_nonempty` is the
  unconditional one to use.
* `descent` --- the hard half, `F₃ ∩ W_B ≤ A_{ωₘ B}`, a Britton normal-form
  argument in `Ω` whose content is the case where `gen β` fails to commute with
  `b_l` because `l` is nonzero on the window.

`omegaInput_of` turns those two into `OmegaInput`, and hence --- through
`Omega.zeta_pi_omega_closures` and
`Omega.benignTF_ASub_evenSupport` --- into four of the seven fields of
`Higman.OperationClosures`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-! ## 0.  One group identity

Conjugating by a product whose two factors commute can be done in either
order.  This is the whole of the algebra in the peeling step: `gen β` is the
`x`, the tail's code is the `y`, and `emb a` is the `z`. -/

theorem conj_swap {G : Type*} [Group G] {x y z : G} (h : Commute x y) :
    y⁻¹ * (x⁻¹ * z * x) * y = x⁻¹ * (y⁻¹ * z * y) * x := by
  have h1 : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
    rw [← mul_inv_rev, h.eq, mul_inv_rev]
  calc y⁻¹ * (x⁻¹ * z * x) * y = y⁻¹ * x⁻¹ * z * (x * y) := by group
    _ = x⁻¹ * y⁻¹ * z * (y * x) := by rw [h1, h.eq]
    _ = x⁻¹ * (y⁻¹ * z * y) * x := by group

/-! ## 1.  The blocks, as a set of sequences

Mikaelian's `ℰ_m`: the sequences supported on the window `[0, m)`.  Every
`m`-block of every sequence is one, and consequently `ωₘ` only ever sees
`B ∩ ℰ_m`. -/

/-- The possible `m`-blocks: sequences supported on `[0, m)`. -/
def blockSet (m : ℕ) : Set E :=
  {f : E | ∀ i : ℤ, i ∉ Finset.Ico (0 : ℤ) (m : ℤ) → f i = 0}

theorem blockAt_mem_blockSet (m : ℕ) (i : ℤ) (f : E) :
    blockAt m i f ∈ blockSet m := by
  intro j hj
  rw [blockAt_apply, if_neg hj]

/-- **`ωₘ` only sees the part of `B` that consists of blocks.**  So nothing is
lost by generating `W_B` from `B ∩ ℰ_m`, which is what Mikaelian's `g_f` are
indexed by. -/
theorem omegaOp_inter_blockSet (m : ℕ) (B : Set E) :
    omegaOp m (B ∩ blockSet m) = omegaOp m B := by
  refine Set.ext fun f => ?_
  constructor
  · intro hf i
    exact (hf i).1
  · intro hf i
    exact ⟨hf i, blockAt_mem_blockSet m i f⟩

/-! ## 2.  Cutting a sequence at the window

The peeling step needs `b_l = b_β · b_t`, with `β` the block at index `0` and
`t` everything from coordinate `m` on.  Both halves are filters, and
`Split.elt_split` factors the code at any threshold, so the only work is
recognizing the low filter as `blockAt m 0`. -/

/-- Everything from coordinate `m` on. -/
noncomputable def tailFrom (m : ℕ) (f : E) : E :=
  Finsupp.filter (fun i : ℤ => ¬ i ≤ (m : ℤ) - 1) f

theorem tailFrom_eq (m : ℕ) (f : E) :
    tailFrom m f = Finsupp.filter (fun i : ℤ => ¬ i ≤ (m : ℤ) - 1) f := rfl

theorem tailFrom_apply_of_lt {m : ℕ} {f : E} {i : ℤ} (h : i < (m : ℤ)) :
    tailFrom m f i = 0 := by
  rw [tailFrom_eq, Finsupp.filter_apply,
    if_neg (not_not_intro (show i ≤ (m : ℤ) - 1 by omega))]

theorem tailFrom_apply_of_le {m : ℕ} {f : E} {i : ℤ} (h : (m : ℤ) ≤ i) :
    tailFrom m f i = f i := by
  rw [tailFrom_eq, Finsupp.filter_apply,
    if_pos (show ¬ i ≤ (m : ℤ) - 1 by omega)]

/-- **The low filter of a nonnegatively supported sequence is its zeroth
block.** -/
theorem filter_low_eq_blockAt_zero {m : ℕ} {l : E}
    (hl : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i) :
    Finsupp.filter (fun i : ℤ => i ≤ (m : ℤ) - 1) l = blockAt m 0 l := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.filter_apply, blockAt_apply]
  rw [show (m : ℤ) * 0 + j = j by ring]
  by_cases hj : (0 : ℤ) ≤ j ∧ j < (m : ℤ)
  · obtain ⟨hj0, hj1⟩ := hj
    rw [if_pos (Finset.mem_Ico.mpr ⟨hj0, hj1⟩),
      if_pos (show j ≤ (m : ℤ) - 1 by omega)]
  · have hnot : j ∉ Finset.Ico (0 : ℤ) (m : ℤ) := fun h => hj (Finset.mem_Ico.mp h)
    rw [if_neg hnot]
    by_cases hjle : j ≤ (m : ℤ) - 1
    · rw [if_pos hjle]
      by_contra hcon
      exact hj ⟨hl j hcon, by omega⟩
    · rw [if_neg hjle]

/-- **The code splits at the window.** -/
theorem bElt_split_block {m : ℕ} {l : E} (hl : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i) :
    bElt l = bElt (blockAt m 0 l) * bElt (tailFrom m l) := by
  have hlow : Finsupp.filter (fun i : ℤ => i ≤ (m : ℤ) - 1) l = blockAt m 0 l :=
    filter_low_eq_blockAt_zero hl
  have h : elt l = elt (blockAt m 0 l) * elt (tailFrom m l) := by
    rw [← hlow, tailFrom_eq]
    exact Split.elt_split ((m : ℤ) - 1) l
  unfold bElt
  rw [h, map_mul]

/-- **The conjugate splits at the window**: `a_l` is `a_β` conjugated by the
code of the tail. -/
theorem aElt_split_block {m : ℕ} {l : E} (hl : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i) :
    aElt l
      = (bElt (tailFrom m l))⁻¹ * aElt (blockAt m 0 l) * bElt (tailFrom m l) := by
  have hb : bElt l = bElt (blockAt m 0 l) * bElt (tailFrom m l) :=
    bElt_split_block hl
  unfold aElt
  rw [hb]
  group

/-! ## 3.  Pushing the tail down by one block

The tail is supported on `[m, ∞)`, so it is the `m`-shift of something, and
that something has one fewer block.  `unshift` is the inverse of `shiftPow m`,
and the two lemmas that matter are that it moves the block index by one
(`blockAt_unshift`) and that the block it vacates is the *zero* block --- which
is why `0 ∈ B` is the hypothesis that makes `ωₘ` non-vacuous. -/

/-- The inverse of `shiftPow m`. -/
noncomputable def unshift (m : ℕ) (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.addRight ((m : ℤ))).symm f

@[simp] theorem unshift_apply (m : ℕ) (f : E) (i : ℤ) :
    unshift m f i = f (i + (m : ℤ)) := by
  unfold unshift
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  rfl

theorem shiftPow_unshift (m : ℕ) (f : E) : shiftPow m (unshift m f) = f := by
  refine Finsupp.ext fun i => ?_
  rw [shiftPow_apply, unshift_apply]
  congr 1
  ring

/-- **Unshifting moves the block index by one.** -/
theorem blockAt_unshift (m : ℕ) (i : ℤ) (f : E) :
    blockAt m i (unshift m f) = blockAt m (i + 1) f := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj, if_pos hj, unshift_apply]
    congr 1
    ring
  · rw [if_neg hj, if_neg hj]

theorem blockAt_tailFrom_of_pos {m : ℕ} {i : ℤ} (hi : 1 ≤ i) (l : E) :
    blockAt m i (tailFrom m l) = blockAt m i l := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj, if_pos hj]
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj0, hj1⟩ := hj
    have hmz : (0 : ℤ) < (m : ℤ) := lt_of_le_of_lt hj0 hj1
    have h1 : (m : ℤ) * 1 ≤ (m : ℤ) * i := mul_le_mul_of_nonneg_left hi hmz.le
    rw [mul_one] at h1
    exact tailFrom_apply_of_le (by linarith)
  · rw [if_neg hj, if_neg hj]

theorem blockAt_tailFrom_of_nonpos {m : ℕ} {i : ℤ} (hi : i ≤ 0) (l : E) :
    blockAt m i (tailFrom m l) = 0 := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj0, hj1⟩ := hj
    have hmz : (0 : ℤ) < (m : ℤ) := lt_of_le_of_lt hj0 hj1
    have h1 : (m : ℤ) * i ≤ (m : ℤ) * 0 := mul_le_mul_of_nonneg_left hi hmz.le
    rw [mul_zero] at h1
    exact tailFrom_apply_of_lt (by linarith)
  · rw [if_neg hj]

/-- **The unshifted tail still has all its blocks in `B`.**  The blocks the
unshift vacates are zero, and that is the one place `0 ∈ B` is used. -/
theorem blockAt_unshift_tailFrom_mem {m : ℕ} {B : Set E} (h0 : (0 : E) ∈ B)
    {l : E} (hl : ∀ i : ℤ, blockAt m i l ∈ B) (i : ℤ) :
    blockAt m i (unshift m (tailFrom m l)) ∈ B := by
  rw [blockAt_unshift]
  by_cases h : i + 1 ≤ 0
  · rw [blockAt_tailFrom_of_nonpos h l]
    exact h0
  · rw [blockAt_tailFrom_of_pos (show (1 : ℤ) ≤ i + 1 by omega) l]
    exact hl (i + 1)

/-- **The unshifted tail is one block shorter.**  This is the measure the
induction of §6 descends on. -/
theorem unshift_tailFrom_bounded {m : ℕ} {bnd : ℤ} {l : E}
    (hbd : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i ∧ i < bnd + (m : ℤ)) (i : ℤ)
    (hi : unshift m (tailFrom m l) i ≠ 0) : 0 ≤ i ∧ i < bnd := by
  rw [unshift_apply] at hi
  have hge : (m : ℤ) ≤ i + (m : ℤ) := by
    by_contra hcon
    have hz : tailFrom m l (i + (m : ℤ)) = 0 := tailFrom_apply_of_lt (by omega)
    exact hi hz
  rw [tailFrom_apply_of_le hge] at hi
  obtain ⟨hb1, hb2⟩ := hbd (i + (m : ℤ)) hi
  exact ⟨by linarith, by linarith⟩

/-! ## 4.  Shifting a whole sequence into the nonnegative range

A finitely supported sequence has a lowest nonzero coordinate, so some iterate
of `shiftPow m` puts it in `[0, m·N)` for some `N`; `mem_omegaOp_shiftPow`
says the shift does not disturb membership in `ωₘ B`. -/

theorem iterate_shiftPow_apply (m p : ℕ) (f : E) (i : ℤ) :
    ((shiftPow m)^[p] f) i = f (i - (m : ℤ) * (p : ℤ)) := by
  induction p generalizing i with
  | zero => simp
  | succ p ih =>
      rw [Function.iterate_succ_apply', shiftPow_apply, ih]
      congr 1
      push_cast
      ring

theorem mem_omegaOp_iterate_shiftPow (m : ℕ) (B : Set E) (p : ℕ) {f : E}
    (hf : f ∈ omegaOp m B) : (shiftPow m)^[p] f ∈ omegaOp m B := by
  induction p with
  | zero => rwa [Function.iterate_zero_apply]
  | succ p ih =>
      rw [Function.iterate_succ_apply']
      exact (mem_omegaOp_shiftPow m B _).mpr ih

theorem exists_nat_mul_gt {m : ℕ} (hm : 0 < m) (M : ℤ) :
    ∃ N : ℕ, M < (m : ℤ) * (N : ℤ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine ⟨N, lt_of_lt_of_le hN ?_⟩
  have hmz : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hmz

/-- **Every sequence can be shifted into a window `[0, m·N)`.** -/
theorem exists_shift_bound {m : ℕ} (hm : 0 < m) (l : E) :
    ∃ p N : ℕ, ∀ i : ℤ,
      ((shiftPow m)^[p] l) i ≠ 0 → 0 ≤ i ∧ i < (m : ℤ) * (N : ℤ) := by
  classical
  obtain ⟨M, hM⟩ := l.support.exists_le
  obtain ⟨M', hM'⟩ := (l.support.image (fun i : ℤ => -i)).exists_le
  obtain ⟨p, hp⟩ := exists_nat_mul_gt hm M'
  obtain ⟨N, hN⟩ := exists_nat_mul_gt hm (M + (m : ℤ) * (p : ℤ))
  refine ⟨p, N, ?_⟩
  intro i hi
  rw [iterate_shiftPow_apply] at hi
  have hsupp : i - (m : ℤ) * (p : ℤ) ∈ l.support := Finsupp.mem_support_iff.mpr hi
  have h1 : i - (m : ℤ) * (p : ℤ) ≤ M := hM _ hsupp
  have h2 : -(i - (m : ℤ) * (p : ℤ)) ≤ M' :=
    hM' _ (Finset.mem_image.mpr ⟨i - (m : ℤ) * (p : ℤ), hsupp, rfl⟩)
  exact ⟨by linarith, by linarith⟩

/-! ## 5.  The tower, as an interface

Everything the closure computation uses about `Ω` is here.  A concrete
`Tower m` is Mikaelian's `Σ → Π → Ω`; nothing below builds one. -/

/-- **The data of the `ωₘ` tower.**  `G` is `Ω`, `gen β` is `g_β`, `stable` is
`r`, and the three relations are the three stages of the tower. -/
structure Tower (m : ℕ) where
  /-- The top of the tower, Mikaelian's `Ω`. -/
  G : Type
  /-- Its group structure. -/
  [group : Group G]
  /-- `F₃` sits inside it. -/
  emb : F₃ →* G
  /-- ... as a subgroup.  This is what makes `F₃ ∩ W_B` a statement about
  `F₃`. -/
  emb_injective : Function.Injective emb
  /-- The second copy of the coding, `g_β = g^{h_β}`, built from the generators
  `g, h, k` adjoined at the first stage. -/
  gen : E → G
  /-- The stable letter of the last stage, Mikaelian's `r`. -/
  stable : G
  /-- **Third stage.**  `r` conjugates `F₃` by the `m`-shift automorphism
  `ρ : a, b, c ↦ a, b^{c^m}, c`, which is `shiftAut^m`. -/
  conj_stable : ∀ x : F₃, stable⁻¹ * emb x * stable = emb ((⇑shiftAut)^[m] x)
  /-- **Second stage.**  `a` centralizes `L = ⟨g_β b_β⁻¹ : β ∈ ℰ_m⟩`, which
  says exactly that conjugating `a` by `g_β` is the same as conjugating it by
  `b_β`, i.e. gives `a_β`. -/
  conj_gen : ∀ β ∈ blockSet m, (gen β)⁻¹ * emb a * gen β = emb (aElt β)
  /-- **First stage.**  `g, h, k` centralize `B₀ₘ = ⟨bᵢ : i ∉ [0, m)⟩`, so
  every `g_β` commutes with every row outside the window. -/
  commute_row : ∀ β ∈ blockSet m, ∀ i : ℤ, i ∉ Finset.Ico (0 : ℤ) (m : ℤ) →
    Commute (gen β) (emb (rowElt i))

attribute [instance] Tower.group

/-- **Mikaelian's `W_B`**, generated by the second-copy codes of the blocks in
`B`, the generator `a`, and the stable letter `r`.  Only `B ∩ ℰ_m` contributes,
which costs nothing: `omegaOp_inter_blockSet`. -/
def W {m : ℕ} (T : Tower m) (B : Set E) : Subgroup T.G :=
  Subgroup.closure ({T.emb a, T.stable} ∪ T.gen '' (B ∩ blockSet m))

theorem emb_a_mem_W {m : ℕ} (T : Tower m) (B : Set E) : T.emb a ∈ W T B :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_insert _ _))

theorem stable_mem_W {m : ℕ} (T : Tower m) (B : Set E) : T.stable ∈ W T B :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl))

theorem gen_mem_W {m : ℕ} (T : Tower m) {B : Set E} {β : E} (h1 : β ∈ B)
    (h2 : β ∈ blockSet m) : T.gen β ∈ W T B :=
  Subgroup.subset_closure (Set.mem_union_right _ ⟨β, ⟨h1, h2⟩, rfl⟩)

/-! ## 6.  What the three relations compute

The two consequences the induction runs on: `gen β` commutes with the *code*
of any sequence supported off the window (not just with the rows), and the
stable letter conjugates `a_f` to `a_{shift f}`. -/

theorem emb_aElt_eq {m : ℕ} (T : Tower m) (f : E) :
    T.emb (aElt f) = (T.emb (bElt f))⁻¹ * T.emb a * T.emb (bElt f) := by
  unfold aElt
  rw [map_mul, map_mul, map_inv]

/-- **`gen β` commutes with the code of anything supported off the window.**
The rows outside `[0, m)` generate a subgroup, and commuting with a fixed
element is a subgroup condition, so the generator-level relation
`Tower.commute_row` propagates. -/
theorem commute_gen_bElt {m : ℕ} (T : Tower m) {β : E} (hβ : β ∈ blockSet m)
    {f : E} (hf : ∀ i : ℤ, f i ≠ 0 → i ∉ Finset.Ico (0 : ℤ) (m : ℤ)) :
    Commute (T.gen β) (T.emb (bElt f)) := by
  have hmem : elt f ∈ Subgroup.closure
      (FreeGroup.of '' {i : ℤ | i ∉ Finset.Ico (0 : ℤ) (m : ℤ)}) :=
    Split.elt_mem_closure fun i hi => hf i (Finsupp.mem_support_iff.mp hi)
  unfold bElt
  refine Subgroup.closure_induction
    (p := fun z _ => Commute (T.gen β) (T.emb (rowHom z))) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i, hi, rfl⟩
    rw [rowHom_of]
    exact T.commute_row β hβ i hi
  · rw [map_one, map_one]
    exact Commute.one_right _
  · intro x y _ _ hx hy
    rw [map_mul, map_mul]
    exact hx.mul_right hy
  · intro x _ hx
    rw [map_inv, map_inv]
    exact hx.inv_right

/-- **The stable letter shifts the coded conjugate by one block.** -/
theorem emb_aElt_shift {m : ℕ} (T : Tower m) (f : E) :
    T.emb (aElt (shiftPow m f)) = T.stable⁻¹ * T.emb (aElt f) * T.stable := by
  rw [← shiftAut_iterate_aElt m f, T.conj_stable (aElt f)]

theorem emb_aElt_tailFrom {m : ℕ} (T : Tower m) (l : E) :
    T.emb (aElt (tailFrom m l))
      = T.stable⁻¹ * T.emb (aElt (unshift m (tailFrom m l))) * T.stable := by
  have h := emb_aElt_shift T (unshift m (tailFrom m l))
  rwa [shiftPow_unshift] at h

/-- **The peeling step.**  For a nonnegatively supported `l`, the coded
conjugate `a_l` is the coded conjugate of its tail, conjugated by the
second-copy code of its zeroth block.

This is the one step of the argument that uses all three relations at once:
`aElt_split_block` writes `a_l` as `a_β` conjugated by the tail's code,
`conj_gen` replaces `a_β` by `a` conjugated by `gen β`, and `commute_row` --- via
`commute_gen_bElt` --- lets the two conjugations be swapped, because the tail is
supported off the window. -/
theorem emb_aElt_eq_conj {m : ℕ} (T : Tower m) {l : E}
    (hl : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i) :
    T.emb (aElt l)
      = (T.gen (blockAt m 0 l))⁻¹ * T.emb (aElt (tailFrom m l))
          * T.gen (blockAt m 0 l) := by
  have hcomm : Commute (T.gen (blockAt m 0 l)) (T.emb (bElt (tailFrom m l))) := by
    refine commute_gen_bElt T (blockAt_mem_blockSet m 0 l) ?_
    intro i hi hmem
    rw [Finset.mem_Ico] at hmem
    exact hi (tailFrom_apply_of_lt hmem.2)
  calc T.emb (aElt l)
      = (T.emb (bElt (tailFrom m l)))⁻¹ * T.emb (aElt (blockAt m 0 l))
          * T.emb (bElt (tailFrom m l)) := by
        rw [aElt_split_block hl, map_mul, map_mul, map_inv]
    _ = (T.emb (bElt (tailFrom m l)))⁻¹
          * ((T.gen (blockAt m 0 l))⁻¹ * T.emb a * T.gen (blockAt m 0 l))
          * T.emb (bElt (tailFrom m l)) := by
        rw [T.conj_gen (blockAt m 0 l) (blockAt_mem_blockSet m 0 l)]
    _ = (T.gen (blockAt m 0 l))⁻¹
          * ((T.emb (bElt (tailFrom m l)))⁻¹ * T.emb a
              * T.emb (bElt (tailFrom m l)))
          * T.gen (blockAt m 0 l) := conj_swap hcomm
    _ = (T.gen (blockAt m 0 l))⁻¹ * T.emb (aElt (tailFrom m l))
          * T.gen (blockAt m 0 l) := by
        rw [emb_aElt_eq T (tailFrom m l)]

/-! ## 7.  The easy half of `F₃ ∩ W_B = A_{ωₘ B}`

The induction: a sequence supported on `[0, m·N)` all of whose blocks lie in
`B` has `a_l ∈ W_B`, by peeling one block and unshifting.  Then an arbitrary
sequence is shifted into such a window, and the shift is undone by conjugating
by a power of the stable letter, which is in `W_B`. -/

theorem emb_aElt_mem_W_of_bounded {m : ℕ} (T : Tower m) {B : Set E}
    (h0 : (0 : E) ∈ B) :
    ∀ (N : ℕ) (l : E), (∀ i : ℤ, l i ≠ 0 → 0 ≤ i ∧ i < (m : ℤ) * (N : ℤ)) →
      (∀ i : ℤ, blockAt m i l ∈ B) → T.emb (aElt l) ∈ W T B := by
  intro N
  induction N with
  | zero =>
      intro l hbd _
      have hlz : l = 0 := by
        refine Finsupp.ext fun i => ?_
        rw [Finsupp.coe_zero, Pi.zero_apply]
        by_contra hcon
        obtain ⟨hi0, hi1⟩ := hbd i hcon
        have hi2 : i < 0 := by simpa using hi1
        exact absurd hi2 (not_lt.mpr hi0)
      rw [hlz, aElt_zero]
      exact emb_a_mem_W T B
  | succ N ih =>
      intro l hbd hblk
      have hbd' : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i ∧ i < (m : ℤ) * (N : ℤ) + (m : ℤ) := by
        intro i hi
        have h := hbd i hi
        have hcast : (m : ℤ) * ((N + 1 : ℕ) : ℤ) = (m : ℤ) * (N : ℤ) + (m : ℤ) := by
          push_cast
          ring
        rw [hcast] at h
        exact h
      have hl0 : ∀ i : ℤ, l i ≠ 0 → 0 ≤ i := fun i hi => (hbd' i hi).1
      have hgen : T.gen (blockAt m 0 l) ∈ W T B :=
        gen_mem_W T (hblk 0) (blockAt_mem_blockSet m 0 l)
      have hst : T.stable ∈ W T B := stable_mem_W T B
      have hu : T.emb (aElt (unshift m (tailFrom m l))) ∈ W T B :=
        ih (unshift m (tailFrom m l))
          (fun i hi => unshift_tailFrom_bounded hbd' i hi)
          (fun i => blockAt_unshift_tailFrom_mem h0 hblk i)
      rw [emb_aElt_eq_conj T hl0, emb_aElt_tailFrom T l]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgen)
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hst) hu) hst))
        hgen

theorem emb_aElt_mem_W_of_iterate {m : ℕ} (T : Tower m) {B : Set E} :
    ∀ (p : ℕ) (l : E), T.emb (aElt ((shiftPow m)^[p] l)) ∈ W T B →
      T.emb (aElt l) ∈ W T B := by
  intro p
  induction p with
  | zero =>
      intro l h
      rwa [Function.iterate_zero_apply] at h
  | succ p ih =>
      intro l h
      rw [Function.iterate_succ_apply', emb_aElt_shift] at h
      refine ih l ?_
      have hst : T.stable ∈ W T B := stable_mem_W T B
      have hres : T.emb (aElt ((shiftPow m)^[p] l))
          = T.stable * (T.stable⁻¹ * T.emb (aElt ((shiftPow m)^[p] l)) * T.stable)
              * T.stable⁻¹ := by group
      have hmem := Subgroup.mul_mem _ (Subgroup.mul_mem _ hst h)
        (Subgroup.inv_mem _ hst)
      rwa [← hres] at hmem

/-- **Every coded conjugate of a sequence in `ωₘ B` lies in `W_B`.** -/
theorem emb_aElt_mem_W {m : ℕ} (hm : 0 < m) (T : Tower m) {B : Set E}
    (h0 : (0 : E) ∈ B) {l : E} (hl : l ∈ omegaOp m B) :
    T.emb (aElt l) ∈ W T B := by
  obtain ⟨p, N, hpN⟩ := exists_shift_bound hm l
  refine emb_aElt_mem_W_of_iterate T p l ?_
  exact emb_aElt_mem_W_of_bounded T h0 N ((shiftPow m)^[p] l) hpN
    (mem_omegaOp_iterate_shiftPow m B p hl)

/-- **The easy half of Mikaelian's computation**, `A_{ωₘ B} ≤ F₃ ∩ W_B`. -/
theorem ASub_omegaOp_le {m : ℕ} (hm : 0 < m) (T : Tower m) {B : Set E}
    (h0 : (0 : E) ∈ B) : ASub (omegaOp m B) ≤ (W T B).comap T.emb := by
  unfold ASub
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨l, hl, rfl⟩
  exact Subgroup.mem_comap.mpr (emb_aElt_mem_W hm T h0 hl)

/-! ## 8.  What the tower still owes, and what it buys

Two obligations, both about a *concrete* tower built over the benign witness
for `A_B`.  Neither is proved here, and nothing inhabits `TowerClosure` or
`OmegaTowerInput`.

`benignTF_W_of_gen` cuts the first one down to its real content.  `W_B` is a
join of two subgroups, one of them generated by the two elements `a` and `r`;
so once the tower is finitely presented and torsion-free --- which is what the
three HNN stages give --- all that is left is that `⟨g_β : β ∈ B ∩ ℰ_m⟩` is
benign, and *that* is `A_B` benign transported along the isomorphism carrying
`a, b, c` to `g, h, k`.  This is Mikaelian's last sentence, in Lean. -/

/-- **The benignness obligation reduces to the second copy of `A_B`.**  The
part of `W_B` that is not `⟨g_β⟩` is the two-generator subgroup `⟨a, r⟩`, and a
finitely generated subgroup of a finitely presented torsion-free group is
benign outright. -/
theorem benignTF_W_of_gen {m : ℕ} (T : Tower m) {B : Set E}
    (hfp : Group.IsFinitelyPresented T.G) (hTF : IsPowerTorsionFree T.G)
    (hgen : BenignTF (Subgroup.closure (T.gen '' (B ∩ blockSet m)))) :
    BenignTF (W T B) := by
  letI : Group.IsFinitelyPresented T.G := hfp
  letI : Group.FG T.G :=
    ProductFinitePresentation.fg_of_isFinitelyPresented T.G
  have hfin : (Subgroup.closure ({T.emb a, T.stable} : Set T.G)).FG := by
    refine (Subgroup.fg_iff _).mpr ⟨{T.emb a, T.stable}, rfl, ?_⟩
    exact (Set.finite_singleton _).insert _
  have hW : W T B = Subgroup.closure ({T.emb a, T.stable} : Set T.G)
      ⊔ Subgroup.closure (T.gen '' (B ∩ blockSet m)) := by
    unfold W
    rw [Subgroup.closure_union]
  rw [hW]
  exact BenignTF.sup (benignTF_of_fg hTF hfin) hgen

/-- **The two facts about a tower that this file does not prove.** -/
structure TowerClosure {m : ℕ} (T : Tower m) (B : Set E) : Prop where
  /-- `W_B` is benign in `Ω`, with a torsion-free witness.  This is where the
  tower is built over the benign witness for `A_B`, and where finite
  presentation and torsion-freeness of the three stages are discharged. -/
  benign : BenignTF (W T B)
  /-- The hard half of `F₃ ∩ W_B = A_{ωₘ B}`: a Britton normal-form descent in
  `Ω`, whose content is that `g_β` fails to commute with `b_l` when `l` is
  nonzero on the window `[0, m)`. -/
  descent : ∀ x : F₃, T.emb x ∈ W T B → x ∈ ASub (omegaOp m B)

/-- **Mikaelian's computation `F₃ ∩ W_B = A_{ωₘ B}`**, given the descent. -/
theorem comap_W_eq {m : ℕ} (hm : 0 < m) (T : Tower m) {B : Set E}
    (h0 : (0 : E) ∈ B)
    (hd : ∀ x : F₃, T.emb x ∈ W T B → x ∈ ASub (omegaOp m B)) :
    (W T B).comap T.emb = ASub (omegaOp m B) :=
  le_antisymm (fun x hx => hd x (Subgroup.mem_comap.mp hx))
    (ASub_omegaOp_le hm T h0)

/-- `F₃` is its own torsion-free finitely presented overgroup, which is what
`BenignTF.comap` needs to pull benignness back along `emb`. -/
def selfOvergroup : TorsionFreeFPOvergroup F₃ where
  K := F₃
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree
  emb := MonoidHom.id F₃
  emb_injective := fun _ _ h => h

/-- **The `ωₘ` closure from a tower.**  Benignness of `W_B` pulls back along
`emb` to benignness of `F₃ ∩ W_B`, and the computation identifies that with
`A_{ωₘ B}`. -/
theorem benignTF_ASub_omegaOp_of_tower {m : ℕ} (hm : 0 < m) (T : Tower m)
    {B : Set E} (h0 : (0 : E) ∈ B) (hc : TowerClosure T B) :
    BenignTF (ASub (omegaOp m B)) := by
  have h := BenignTF.comap selfOvergroup T.emb hc.benign
  rwa [comap_W_eq hm T h0 hc.descent] at h

/-- **Input: the tower exists, with its two properties.**

This is `OmegaInput` repackaged as a statement about Mikaelian's construction
rather than about the operation.  The gain is that it is a statement someone
can build: the group is named, the subgroup is named, and the two obligations
are separated into a benignness one and a normal-form one.

**Nothing inhabits this structure.** -/
structure OmegaTowerInput : Prop where
  /-- For every positive `m` and every `B` containing the zero sequence with
  `A_B` benign, the three-stage tower exists and has both properties. -/
  tower : ∀ (m : ℕ), 0 < m → ∀ B : Set E, (0 : E) ∈ B → BenignTF (ASub B) →
    ∃ T : Tower m, TowerClosure T B

/-- **The tower input discharges `OmegaInput`.** -/
theorem omegaInput_of (h : OmegaTowerInput) : OmegaInput :=
  ⟨fun m hm B h0 hB => by
    obtain ⟨T, hc⟩ := h.tower m hm B h0 hB
    exact benignTF_ASub_omegaOp_of_tower hm T h0 hc⟩

/-- **Four of the seven `OperationClosures` fields, from the tower input.**

`zeta`, `pi` and `omega` are `Omega.zeta_pi_omega_closures`; the fourth,
`theta`, gets its `A_{oddZero}` from `Omega.benignTF_ASub_evenSupport`, which
is `ω₂` of `ζ Z` and so also runs off this input alone. -/
theorem zeta_pi_omega_closures_of_tower
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzeta : BenignTF (Agree.rowSub Agree.zetaV)) (h : OmegaTowerInput) :
    (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (zetaOp B)))
      ∧ (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (piOp B)))
      ∧ (∀ (m : ℕ), 0 < m → ∀ (B : Set E), BenignTF (ASub B) →
          BenignTF (ASub (omegaOp m B))) :=
  zeta_pi_omega_closures hhalf hzeta (omegaInput_of h)

end Omega
end Higman
end GroupApproximation
