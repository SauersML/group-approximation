import GroupApproximation.Higman.AgreeClosure

/-!
# Higman's operation `ωₘ`

`ωₘ B` is the set of sequences **all** of whose `m`-blocks lie in `B`.  Unlike
`ζ` and `π`, which enlarge a set and so correspond to a *join* on the group
side (`Higman.Agree`), this one is an intersection over `i : ℤ` of cylinder
conditions, and infinitely many of them.  That is why it is the deepest of the
nine, and it is the only one of the six open closures that this file does not
reduce to the benign calculus.

What *is* proved here:

* `blockAt_apply`, `omegaOp_eq_iInter` --- the operation is the intersection of
  the cylinders `Cᵢ = {f | blockAt m i f ∈ B}`.
* `blockAt_shiftPow`, `mem_omegaOp_shiftPow` --- **the shift by `m` fixes
  `ωₘ B`.**  The cylinders are permuted by it, `Cᵢ₊₁ = σᵐ Cᵢ`, so `ωₘ B` is
  invariant, and hence so is `A_{ωₘ B}` under the automorphism `shiftAut ^ m`
  of `F₃` (`Higman.ShiftOperation`).  This is the structural fact any proof of
  the closure has to use: the intersection is over one orbit, not over an
  arbitrary family.
* `exists_blockAt_eq_zero`, `omegaOp_eq_empty` --- a finitely supported
  sequence has a zero block, so **the closure holds outright when `0 ∉ B`**:
  `ωₘ B` is then empty and `A_∅ = ⊥`.  That is `benignTF_ASub_omegaOp_of_notMem`
  below, proved.

So the operation splits into a proved half and one residue, `OmegaInput`, whose
statement may assume `0 ∈ B`.

## Why the residue is not a corollary of the benign calculus

Higman's calculus (`Higman.Benign`, `Higman.BenignJoin`, `Higman.Coord`) closes
benign subgroups under *finite* meets and joins, images under injective
endomorphisms and preimages.  An intersection over an infinite orbit is none of
these: benign subgroups are not closed under infinite meets, so no rearranging
of `omegaOp_eq_iInter` can discharge it.  What the orbit structure buys is that
the residue is an *HNN* statement rather than a family statement --- with `t`
the stable letter of `F₃ ∗_{shiftAut ^ m} t`, which is finitely presented
because `shiftAut` is an automorphism, the invariant subgroup `A_{ωₘ B}` is
exactly the part of `A_{C₀}` that survives every `t`-translate, and
`Higman.HNNDescent.closure_inf_range` is the descent lemma stated for exactly
that shape.  Turning "survives every translate" into a *finitely generated*
subgroup of the extension is the content of the residue, and it is Higman's
own argument for `ω`; it is not attempted here, and no declaration below
pretends otherwise.

**Nothing inhabits `OmegaInput`.**
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-! ## 1.  Blocks -/

@[simp] theorem blockAt_apply (m : ℕ) (i : ℤ) (f : E) (j : ℤ) :
    blockAt m i f j = if j ∈ Finset.Ico (0 : ℤ) (m : ℤ) then f ((m : ℤ) * i + j) else 0 :=
  Finsupp.onFinset_apply

/-- The operation is the intersection of the block cylinders. -/
theorem omegaOp_eq_iInter (m : ℕ) (B : Set E) :
    omegaOp m B = ⋂ i : ℤ, {f : E | blockAt m i f ∈ B} := by
  refine Set.ext fun f => ?_
  rw [Set.mem_iInter]
  exact Iff.rfl

/-! ## 2.  The shift by `m` permutes the blocks -/

/-- The shift of a sequence by `m` places. -/
noncomputable def shiftPow (m : ℕ) (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.addRight (m : ℤ)) f

@[simp] theorem shiftPow_apply (m : ℕ) (f : E) (i : ℤ) :
    shiftPow m f i = f (i - (m : ℤ)) := by
  unfold shiftPow
  rw [Finsupp.equivMapDomain_apply]
  rfl

/-- **The shift by `m` moves each block one place along.** -/
theorem blockAt_shiftPow (m : ℕ) (i : ℤ) (f : E) :
    blockAt m i (shiftPow m f) = blockAt m (i - 1) f := by
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj, if_pos hj, shiftPow_apply]
    congr 1
    ring
  · rw [if_neg hj, if_neg hj]

/-- **`ωₘ B` is invariant under the shift by `m`.** -/
theorem mem_omegaOp_shiftPow (m : ℕ) (B : Set E) (f : E) :
    shiftPow m f ∈ omegaOp m B ↔ f ∈ omegaOp m B := by
  constructor
  · intro h i
    have := h (i + 1)
    rwa [blockAt_shiftPow, add_sub_cancel_right] at this
  · intro h i
    rw [blockAt_shiftPow]
    exact h (i - 1)

/-! ## 3.  A finitely supported sequence has a zero block -/

theorem exists_blockAt_eq_zero (m : ℕ) (f : E) : ∃ i : ℤ, blockAt m i f = 0 := by
  obtain ⟨N, hN⟩ := f.support.exists_le
  refine ⟨max N 0 + 1, ?_⟩
  refine Finsupp.ext fun j => ?_
  rw [blockAt_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hm : (1 : ℤ) ≤ (m : ℤ) := by omega
    have hmax : (0 : ℤ) ≤ max N 0 := le_max_right _ _
    have hipos : (0 : ℤ) ≤ max N 0 + 1 := by omega
    have hle : max N 0 + 1 ≤ (m : ℤ) * (max N 0 + 1) := le_mul_of_one_le_left hipos hm
    have hNle : N ≤ max N 0 := le_max_left _ _
    have hgt : N < (m : ℤ) * (max N 0 + 1) + j := by omega
    by_contra hcon
    exact absurd (hN _ (Finsupp.mem_support_iff.mpr hcon)) (not_le.mpr hgt)
  · rw [if_neg hj]

/-- **When `0 ∉ B` the operation is empty**, because almost every block of a
finitely supported sequence is zero. -/
theorem omegaOp_eq_empty (m : ℕ) {B : Set E} (h0 : (0 : E) ∉ B) :
    omegaOp m B = (∅ : Set E) := by
  refine Set.ext fun f => ?_
  rw [Set.mem_empty_iff_false, iff_false]
  intro hf
  obtain ⟨i, hi⟩ := exists_blockAt_eq_zero m f
  exact h0 (hi ▸ hf i)

/-- **Higman's `ωₘ` closure, proved in the case `0 ∉ B`.** -/
theorem benignTF_ASub_omegaOp_of_notMem (m : ℕ) {B : Set E} (h0 : (0 : E) ∉ B) :
    BenignTF (ASub (omegaOp m B)) := by
  rw [omegaOp_eq_empty m h0]
  exact benignTF_ASub_empty

/-! ## 4.  What is still owed -/

/-- **Input: Higman's operation `ωₘ`, in the only case that is open.**

The hypothesis `0 ∈ B` costs nothing --- `benignTF_ASub_omegaOp_of_notMem`
settles the other case --- and it is what makes the statement non-vacuous: with
it, all but finitely many of the block conditions on a given sequence hold
automatically.

**Nothing inhabits this structure.** -/
structure OmegaInput where
  /-- Closure under `ωₘ`, given that the zero sequence is in `B`. -/
  omega : ∀ (m : ℕ) (B : Set E), (0 : E) ∈ B → BenignTF (ASub B) →
    BenignTF (ASub (omegaOp m B))

/-- **Higman's operation `ωₘ` preserves benignness**, given the residue. -/
theorem benignTF_ASub_omegaOp (h : OmegaInput) (m : ℕ) (B : Set E)
    (hB : BenignTF (ASub B)) : BenignTF (ASub (omegaOp m B)) := by
  by_cases h0 : (0 : E) ∈ B
  · exact h.omega m B h0 hB
  · exact benignTF_ASub_omegaOp_of_notMem m h0

/-! ## 5.  The three closures, in the shape `OperationClosures` asks for

`Higman.OperationClosures` (`Higman/Operations.lean`) lists six open closures.
This theorem is exactly the last three of its fields --- `zeta`, `pi`,
`omega` --- derived from the four named inputs of this workstream:
`Agree.AgreeInputs` (the positive half-row, the normal closure of `b` in the
row, and the subgroup of all coded sequences) and `OmegaInput`.  The first
three fields, `rho`, `tau` and `theta`, are a separate workstream and are not
touched here. -/
theorem zeta_pi_omega_closures (h : Agree.AgreeInputs) (k : OmegaInput) :
    (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (zetaOp B)))
      ∧ (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (piOp B)))
      ∧ (∀ (m : ℕ) (B : Set E), BenignTF (ASub B) →
          BenignTF (ASub (omegaOp m B))) :=
  ⟨fun B hB => Agree.benignTF_ASub_zetaOp h B hB,
    fun B hB => Agree.benignTF_ASub_piOp h B hB,
    fun m B hB => benignTF_ASub_omegaOp k m B hB⟩

end Omega
end Higman
end GroupApproximation
