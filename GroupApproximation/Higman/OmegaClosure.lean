import GroupApproximation.Higman.AgreeClosure
import GroupApproximation.Higman.GeneratedBasic

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
the residue is a statement about *one orbit* rather than about an arbitrary
family: `mem_omegaOp_shiftPow` says the shift by `m` permutes the cylinders, so
`A_{ωₘ B}` is invariant under the automorphism `shiftAut ^ m` of `F₃`.

**Which construction discharges it is not decided here, and the obvious one is
not the recommended one.**  A single HNN extension `F₃ ∗_{shiftAut ^ m} t` with
`Higman.HNNDescent.closure_inf_range` is the shape the invariance suggests, but
it computes a *union* over the orbit, not the intersection this operation
needs, so it does not discharge the residue by itself.  The route to follow is
the three-stage normal-form analysis of the modern write-up (Mikaelian,
arXiv:1908.10153, §4) --- the chain `Σ = K ∗_P (g,h,k)`, `Π = M ∗_R a`,
`Ω = Π ∗_ρ r`, with `W_B = ⟨g_f, a, r⟩` and the computation `F ∩ W_B = A_{ωₘ B}`.
That analysis exists precisely because Higman's own §4 leaves this step to the
reader (p. 472); his `M ∗ K` construction should **not** be followed.  None of
it is attempted here, and no declaration below pretends otherwise.

**Nothing inhabits `OmegaInput`.**
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open scoped Pointwise

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

/-! ## 2b.  Blocks are windows of the coding

Whatever construction discharges the residue, it has to say what the code of a
block is in terms of the code of the sequence, because `omegaOp` is defined
through `blockAt` while `ASub` is defined through `elt`.  These two lemmas are
that bridge, and they are route-independent: the `m`-block at `i` is the
window of `f` on `[mi, mi+m)` carried back to `[0, m)`, and the *code* of that
window is what the deletion retraction `Split.killOn` reads off the code of
`f`. -/

/-- The window predicate cutting out the `m`-block at `i`. -/
def blockWindow (m : ℕ) (i : ℤ) : ℤ → Prop :=
  fun j => (m : ℤ) * i ≤ j ∧ j < (m : ℤ) * i + (m : ℤ)

instance (m : ℕ) (i : ℤ) : DecidablePred (blockWindow m i) := fun _ => by
  unfold blockWindow
  infer_instance

/-- **A block is a translated window.** -/
theorem blockAt_eq_filter_translate (m : ℕ) (i : ℤ) (f : E) :
    blockAt m i f
      = Finsupp.equivMapDomain (Equiv.addRight (-((m : ℤ) * i)))
          (Finsupp.filter (blockWindow m i) f) := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.equivMapDomain_apply, blockAt_apply, Finsupp.filter_apply]
  have hsymm : (Equiv.addRight (-((m : ℤ) * i))).symm j = j + (m : ℤ) * i := by
    show j - -((m : ℤ) * i) = j + (m : ℤ) * i
    ring
  rw [hsymm]
  by_cases hj : (0 : ℤ) ≤ j ∧ j < ((m : ℕ) : ℤ)
  · rw [if_pos (Finset.mem_Ico.mpr hj), if_pos (show blockWindow m i (j + (m : ℤ) * i) by
      unfold blockWindow; omega)]
    congr 1
    ring
  · rw [if_neg (fun h => hj (Finset.mem_Ico.mp h)),
      if_neg (show ¬ blockWindow m i (j + (m : ℤ) * i) by unfold blockWindow; omega)]

/-- **The code of a block's window is read off the code of `f` by deleting the
coordinates outside it.** -/
theorem killOn_blockWindow_elt (m : ℕ) (i : ℤ) (f : E) :
    Split.killOn (blockWindow m i) (elt f)
      = elt (Finsupp.filter (blockWindow m i) f) :=
  Split.killOn_elt _ f

/-! ## 2c.  The third stage's map is the `m`-shift, and it is safe here

The modern write-up's third stage is an HNN extension along the automorphism of
`F₃ = ⟨a, b, c⟩` fixing `a` and `c` and sending `b` to `b^{c^m}` --- the
`m`-shift of the row, `shiftAut^[m]` in this repository's names.  Its use is a
computation `(a^{b_l})^r = a^{b_{l'}}` with `l'` the `m`-shift of `l`, and that
is the one place in the `ωₘ` argument where an automorphism is asked to carry
an **ordered** product `b_f` to another ordered product.

That is worth proving rather than assuming, because the same move is what
fails elsewhere in the same section: an automorphism can act correctly on the
generators `bᵢ` and still act incorrectly on `b_f`, since `b_f` is the product
over the support taken in INCREASING order.  Here it is sound, and for the one
reason that matters --- `i ↦ i + m` is order-PRESERVING, so it commutes with
the sort defining `elt` (`Seq.sort_map_add`), which is exactly why `σ` closes
in `Higman.ShiftOperation` while an order-reversing relabelling does not.

`shiftAut_iterate_aElt` below is the computation in the form the construction
uses it. -/

theorem shiftPow_zero (f : E) : shiftPow 0 f = f := by
  refine Finsupp.ext fun i => ?_
  rw [shiftPow_apply, Nat.cast_zero, sub_zero]

theorem shiftSeq_shiftPow (m : ℕ) (f : E) :
    shiftSeq (shiftPow m f) = shiftPow (m + 1) f := by
  refine Finsupp.ext fun i => ?_
  rw [shiftSeq_apply, shiftPow_apply, shiftPow_apply]
  congr 1
  push_cast
  ring

/-- **The `m`-fold shift automorphism carries the coded sequence to the coded
`m`-shift.**  The order-preserving relabelling survives the sort. -/
theorem shiftAut_iterate_bElt (m : ℕ) (f : E) :
    (⇑shiftAut)^[m] (bElt f) = bElt (shiftPow m f) := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, shiftPow_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, shiftAut_bElt, shiftSeq_shiftPow]

/-- **The same on the conjugates**, which is the form the third stage uses:
`a^{b_l}` goes to `a^{b_{l'}}` with `l'` the `m`-shift of `l`. -/
theorem shiftAut_iterate_aElt (m : ℕ) (f : E) :
    (⇑shiftAut)^[m] (aElt f) = aElt (shiftPow m f) := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, shiftPow_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, shiftAut_aElt, shiftSeq_shiftPow]

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

The hypothesis `0 < m` is Higman's own restriction (Theorem 3 quantifies `ωₘ`
over *positive* `m`), and dropping it would make this structure strictly
stronger than anything in the literature.  At `m = 0` the block index set
`Finset.Ico 0 0` is empty, so `blockAt 0 i f = 0` for every `i` and `f`, and
`omegaOp 0 B` is the whole space whenever `0 ∈ B`.  An unrestricted field would
therefore hand out `BenignTF (ASub Set.univ)` --- benignness of `A_E` --- from
any `B` containing the zero sequence, and neither Higman's Lemma 4.10 nor the
modern write-up covers that case: both assume `m ≥ 1`.  Restricting here keeps
the residue priced at what the sources actually prove.

**Nothing inhabits this structure.** -/
structure OmegaInput where
  /-- Closure under `ωₘ` for positive `m`, given that the zero sequence is
  in `B`. -/
  omega : ∀ (m : ℕ), 0 < m → ∀ (B : Set E), (0 : E) ∈ B → BenignTF (ASub B) →
    BenignTF (ASub (omegaOp m B))

/-- **Higman's operation `ωₘ` preserves benignness**, given the residue. -/
theorem benignTF_ASub_omegaOp (h : OmegaInput) (m : ℕ) (hm : 0 < m) (B : Set E)
    (hB : BenignTF (ASub B)) : BenignTF (ASub (omegaOp m B)) := by
  by_cases h0 : (0 : E) ∈ B
  · exact h.omega m hm B h0 hB
  · exact benignTF_ASub_omegaOp_of_notMem m h0

/-! ## 5.  `Agree.AgreeInputs.all` is not an independent input

The subgroup of all coded sequences is benign as soon as `ωₘ` is, because
`Set.univ` is `ω₁` of an **explicitly benign** set.  `ζ Z` is the set of
sequences supported in `{0}`, whose coded index set is the cyclic group
`⟨b⟩`, so `A_{ζ Z} = (⟨a⟩ ⊔ ⟨b⟩) ⊓ ker retK` by `Coord.Aset_mul_subgroup` ---
a join of two finitely generated subgroups of a finitely presented
torsion-free group, met with a benign kernel.  And every `1`-block of every
sequence is supported in `{0}`, so `ω₁` imposes no condition at all.

So the three inputs of `Agree.AgreeInputs` reduce to two, plus `OmegaInput`.

The two set-level identities this needs --- `Seq.zetaOp_Zset : ζ Z = atZero` and
`Seq.omegaOp_one_atZero : ω₁ atZero = univ` --- are `Higman.GeneratedBasic`'s,
not restated here. -/

theorem zero_mem_zetaOp_Zset : (0 : E) ∈ zetaOp Zset := ⟨0, rfl, fun _ _ => rfl⟩

theorem rowElt_zero : rowElt 0 = b := by
  unfold rowElt
  group

/-- **The coded index set of `ζ Z` is the cyclic group `⟨b⟩`.** -/
theorem bElt_image_zetaOp_Zset :
    bElt '' (zetaOp Zset) = (Subgroup.closure ({b} : Set F₃) : Set F₃) := by
  refine Set.ext fun x => ?_
  rw [zetaOp_Zset]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hf' : ∀ i : ℤ, i ≠ 0 → f i = 0 := hf
    have hsupp : ∀ i ∈ f.support, i ∈ [(0 : ℤ)] := by
      intro i hi
      by_contra hcon
      exact Finsupp.mem_support_iff.mp hi (hf' i (by simpa using hcon))
    have hcode : elt f = FreeGroup.of (0 : ℤ) ^ f 0 := by
      rw [Split.elt_eq_eltOn (by simp) (by simp) hsupp]
      rw [Split.eltOn_cons, Split.eltOn_nil, mul_one]
    rw [SetLike.mem_coe, Subgroup.mem_closure_singleton]
    refine ⟨f 0, ?_⟩
    rw [Agree.bElt_eq_rowHom, hcode, map_zpow, rowHom_of, rowElt_zero]
  · intro hx
    rw [SetLike.mem_coe, Subgroup.mem_closure_singleton] at hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨Finsupp.single (0 : ℤ) n, ?_, ?_⟩
    · show ∀ i : ℤ, i ≠ 0 → (Finsupp.single (0 : ℤ) n) i = 0
      intro i hi
      rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    · have hsupp : ∀ i ∈ (Finsupp.single (0 : ℤ) n).support, i ∈ [(0 : ℤ)] := by
        intro i hi
        simpa using Finsupp.support_single_subset hi
      have hcode : elt (Finsupp.single (0 : ℤ) n)
          = FreeGroup.of (0 : ℤ) ^ (Finsupp.single (0 : ℤ) n) 0 := by
        rw [Split.elt_eq_eltOn (by simp) (by simp) hsupp]
        rw [Split.eltOn_cons, Split.eltOn_nil, mul_one]
      rw [Agree.bElt_eq_rowHom, hcode, map_zpow, rowHom_of, rowElt_zero,
        Finsupp.single_eq_same]

/-- **`A_{ζ Z}` is benign outright.** -/
theorem benignTF_ASub_zetaOp_Zset : BenignTF (ASub (zetaOp Zset)) := by
  have hone : ({1} : Set F₃) * (Subgroup.closure ({b} : Set F₃) : Set F₃)
      = (Subgroup.closure ({b} : Set F₃) : Set F₃) := by
    refine Set.ext fun x => ?_
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      show (1 : F₃) * z ∈ (Subgroup.closure ({b} : Set F₃) : Set F₃)
      rwa [one_mul]
    · intro hx
      exact ⟨1, rfl, x, hx, one_mul x⟩
  have hbase : Coord.Aset ({1} : Set F₃) = Subgroup.closure ({a} : Set F₃) := by
    unfold Coord.Aset
    congr 1
    rw [Set.image_singleton]
    have hc : Coord.conjA (1 : F₃) = a := by
      unfold Coord.conjA
      group
    rw [hc]
  have hbK : Subgroup.closure ({b} : Set F₃) ≤ K :=
    (Subgroup.closure_le _).mpr (by
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact b_mem_K)
  have hfgb : (Subgroup.closure ({b} : Set F₃)).FG :=
    (Subgroup.fg_iff _).mpr ⟨{b}, rfl, Set.finite_singleton _⟩
  have hS : ({1} : Set F₃) ⊆ (K : Set F₃) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.one_mem _
  have hA : BenignTF (Coord.Aset ({1} : Set F₃)) := by
    rw [hbase]
    exact benignTF_of_fg IsPowerTorsionFree.of_isMulTorsionFree fg_closure_a
  have hU : BenignTF (Subgroup.closure ({b} : Set F₃)) :=
    benignTF_of_fg IsPowerTorsionFree.of_isMulTorsionFree hfgb
  rw [Coord.ASub_eq_Aset, bElt_image_zetaOp_Zset, ← hone]
  exact Coord.benignTF_Aset_mul hS hbK hA hU

/-- **The third `Agree` input follows from the `ω` input.**

The two set identities are `Higman.GeneratedBasic`'s: `Seq.omegaOp_one_atZero`
(every `1`-block lies in `atZero`, so `ω₁` imposes no condition) and
`Seq.zetaOp_Zset` (`atZero` is `ζ Z`). -/
theorem benignTF_ASub_univ (k : OmegaInput) :
    BenignTF (ASub (Set.univ : Set E)) := by
  rw [← omegaOp_one_atZero, ← zetaOp_Zset]
  exact k.omega 1 one_pos (zetaOp Zset) zero_mem_zetaOp_Zset benignTF_ASub_zetaOp_Zset

/-! ## 5b.  The even-support sequences, also from `OmegaInput` alone

`Higman.OperationClosureTheta` needs `A_{oddZero}` benign, where `oddZero` is
the set of sequences vanishing at every coordinate that is not even, and gets
it from `Set.univ` through the torsion-free image half of Lemma 3.3.  It does
not have to: `oddZero` is `ω₂` of `ζ Z`, exactly as `Set.univ` is `ω₁` of
`ζ Z`, so the SAME residue discharges both, at `m = 2` instead of `m = 1`.

The reason is that a `2`-block is indexed by `{0, 1}`, so it lies in
`ζ Z = atZero` exactly when its entry at `1` vanishes --- and as `i` runs over
`ℤ`, `2i + 1` runs over the coordinates that are not even.  No image closure,
no doubling map, no automorphism of `F₃` is involved. -/

theorem omegaOp_two_zetaOp_Zset :
    omegaOp 2 (zetaOp Zset) = {f : E | ∀ i : ℤ, (∀ k : ℤ, i ≠ 2 * k) → f i = 0} := by
  refine Set.ext fun f => ?_
  constructor
  · intro hf n hn
    have hodd : Odd n := by
      rcases Int.even_or_odd n with he | ho
      · obtain ⟨k, hk⟩ := he
        exact (hn k (by omega)).elim
      · exact ho
    obtain ⟨i, rfl⟩ := hodd
    have h1 : blockAt 2 i f ∈ zetaOp Zset := hf i
    rw [zetaOp_Zset] at h1
    have h2 : blockAt 2 i f 1 = 0 := h1 1 one_ne_zero
    rw [blockAt_apply, if_pos (by rw [Finset.mem_Ico]; omega)] at h2
    have hcast : ((2 : ℕ) : ℤ) * i + 1 = 2 * i + 1 := by push_cast; ring
    rwa [hcast] at h2
  · intro hf i
    rw [zetaOp_Zset]
    intro j hj
    rw [blockAt_apply]
    by_cases hjm : j ∈ Finset.Ico (0 : ℤ) ((2 : ℕ) : ℤ)
    · rw [if_pos hjm]
      rw [Finset.mem_Ico] at hjm
      have hj1 : j = 1 := by omega
      subst hj1
      exact hf _ (fun k => by push_cast; omega)
    · rw [if_neg hjm]

/-- **`A_{oddZero}` is benign from `OmegaInput` alone.**  This is the input
`Higman.OperationClosureTheta.benignTF_ASub_oddZero` obtains from
`TorsionFreeImageClosure`; that lemma is not needed for it. -/
theorem benignTF_ASub_evenSupport (k : OmegaInput) :
    BenignTF (ASub {f : E | ∀ i : ℤ, (∀ k : ℤ, i ≠ 2 * k) → f i = 0}) := by
  rw [← omegaOp_two_zetaOp_Zset]
  exact k.omega 2 (by norm_num) (zetaOp Zset) zero_mem_zetaOp_Zset
    benignTF_ASub_zetaOp_Zset

/-- The `Agree` inputs, assembled from two of them and the `ω` input. -/
theorem agreeInputs_of (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzeta : BenignTF (Agree.rowSub Agree.zetaV)) (k : OmegaInput) :
    Agree.AgreeInputs :=
  ⟨hhalf, hzeta, benignTF_ASub_univ k⟩

/-! ## 6.  The three closures, in the shape `OperationClosures` asks for

`Higman.OperationClosures` (`Higman/Operations.lean`) lists six open closures.
This theorem is exactly the last three of its fields --- `zeta`, `pi`,
`omega` --- derived from **three** named inputs: the positive half-row is
benign (Higman's Example 3.7), the normal closure of `b` in the row is benign,
and `OmegaInput`.  The subgroup of all coded sequences, which the agreement
closures also consume, is not a fourth input: `benignTF_ASub_univ` derives it
from `OmegaInput`.  The first three fields, `rho`, `tau` and `theta`, are a
separate workstream and are not touched here.

The `ω` component carries Higman's `0 < m`, matching the restriction his
Theorem 3 states.  Nothing below needs it except the appeal to the residue:
the `0 ∉ B` half is proved for every `m`, `m = 0` included. -/
theorem zeta_pi_omega_closures (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzeta : BenignTF (Agree.rowSub Agree.zetaV)) (k : OmegaInput) :
    (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (zetaOp B)))
      ∧ (∀ B : Set E, BenignTF (ASub B) → BenignTF (ASub (piOp B)))
      ∧ (∀ (m : ℕ), 0 < m → ∀ (B : Set E), BenignTF (ASub B) →
          BenignTF (ASub (omegaOp m B))) :=
  ⟨fun B hB => Agree.benignTF_ASub_zetaOp (agreeInputs_of hhalf hzeta k) B hB,
    fun B hB => Agree.benignTF_ASub_piOp (agreeInputs_of hhalf hzeta k) B hB,
    fun m hm B hB => benignTF_ASub_omegaOp k m hm B hB⟩

end Omega
end Higman
end GroupApproximation
