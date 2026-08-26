import GroupApproximation.Higman.TheoremFour
import GroupApproximation.Higman.SeqFilter
import GroupApproximation.Higman.OperationClosureTau
import GroupApproximation.Higman.RowKernel
import GroupApproximation.Higman.RowDeletionBenign
import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Algebra.HNNTorsionFree

/-!
# Higman's Section 5: coding and exact decoder-kernel completion

`Higman.TransportSectionFive` (`Higman/TheoremFour.lean`) is the passage from
the coded subgroups `A_B ≤ F₃` to arbitrary recursively enumerable normal
subgroups of free groups of finite rank.  This file proves the algebraic
transport and names the two independent inputs it still consumes.

The companion memo is `notes/W6_TRANSPORT_FIVE_SIZING_2026-08-22.md`, and the
decomposition here is the one priced there.

## The design decision: code the letter into the *position*

A raw word `v = (i₁,ε₁)…(i_k,ε_k)` over the alphabet `Fin (n+1)` is coded by a
sequence with **one block of `n+1` positions per letter**:

    codeSeq v :  (j-1)·(n+1) + (i_j mod (n+1))  ↦  ε_j .

Two consequences, and they are the reason for the choice:

* the occupied positions increase strictly with `j`, so `Seq.elt (codeSeq v)`
  is *already* the sorted product `∏_j (of p_j)^{ε_j}` --- `Seq.elt_add_of_lt`
  and `Split.elt_single` compute it, and no sorting argument is needed;
* **decoding is a homomorphism.**  `decodeHom : FreeGroup ℤ →* FreeGroup (Fin
  (n+1))` sends `of p` to the generator named by `p mod (n+1)`, and
  `decodeHom (elt (codeSeq v)) = rawToFree n v` (`decodeHom_elt_codeSeq`).

Under the naive coding --- position = index, value = letter --- the letters sit
in the *exponents* of `elt f`, and no homomorphism can decode them.  Putting
them in the positions makes the decoding a lift of a map of free bases, and
gives it a homomorphic section `sectionHom` (`of i ↦ of (i : ℤ)`), which is what
the final `comap` runs along.

## What is left, and where it is

* `CodeRE` --- that the code set of a recursively enumerable normal subgroup is
  recursively enumerable.  Computability only.
* `UnConjugation` --- from `⟨a^{b_f} : f ∈ B⟩` benign to `⟨b_f : f ∈ B⟩`
  benign.  **This is Section 5's content**; the memo lists four refuted routes
  to it and the two candidates that survive.

`transportSectionFive_of_parts` composes the two with everything proved here
into `Higman.TransportSectionFive`.
-/

namespace GroupApproximation
namespace Higman
namespace Transport

open GroupApproximation.Higman.Conj

/-! ## 1.  Positions, letters, and the two coding homomorphisms -/

/-- The letter named by a position: its residue modulo the alphabet size. -/
def letterOf (n : ℕ) (p : ℤ) : Fin (n + 1) :=
  ⟨(p % ((n : ℤ) + 1)).toNat, by
    have h0 : (0 : ℤ) < (n : ℤ) + 1 := by positivity
    have h1 : p % ((n : ℤ) + 1) < (n : ℤ) + 1 := Int.emod_lt_of_pos p h0
    have h2 : (0 : ℤ) ≤ p % ((n : ℤ) + 1) := Int.emod_nonneg p (ne_of_gt h0)
    omega⟩

/-- The letter named by a raw index, the way `Higman.rawToFree` reads it. -/
def letterOfNat (n : ℕ) (i : ℕ) : Fin (n + 1) :=
  ⟨i % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The position carrying the `k`-th letter of a word when that letter is the
raw index `i`: the `i`-th slot of the `k`-th block. -/
def pos (n k i : ℕ) : ℤ := (k : ℤ) * ((n : ℤ) + 1) + ((i % (n + 1) : ℕ) : ℤ)

theorem pos_lower (n k i : ℕ) : (k : ℤ) * ((n : ℤ) + 1) ≤ pos n k i := by
  have h : (0 : ℤ) ≤ ((i % (n + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold pos
  linarith

theorem pos_upper (n k i : ℕ) : pos n k i < ((k : ℤ) + 1) * ((n : ℤ) + 1) := by
  have h : ((i % (n + 1) : ℕ) : ℤ) < (n : ℤ) + 1 := by
    exact_mod_cast Nat.mod_lt i (Nat.succ_pos n)
  have hexp : ((k : ℤ) + 1) * ((n : ℤ) + 1)
      = (k : ℤ) * ((n : ℤ) + 1) + ((n : ℤ) + 1) := by ring
  unfold pos
  rw [hexp]
  linarith

/-- **A position names the letter it was built from.** -/
theorem letterOf_pos (n k i : ℕ) : letterOf n (pos n k i) = letterOfNat n i := by
  refine Fin.ext ?_
  show ((pos n k i) % ((n : ℤ) + 1)).toNat = i % (n + 1)
  have hform : pos n k i = ((i % (n + 1) : ℕ) : ℤ) + ((n : ℤ) + 1) * (k : ℤ) := by
    unfold pos
    ring
  have hres : (pos n k i) % ((n : ℤ) + 1) = ((i % (n + 1) : ℕ) : ℤ) := by
    rw [hform, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast Nat.mod_lt i (Nat.succ_pos n))
  rw [hres]
  omega

/-- **The decoding homomorphism.**  A position is read as the generator its
residue names. -/
def decodeHom (n : ℕ) : FreeGroup ℤ →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.lift fun p => FreeGroup.of (letterOf n p)

@[simp] theorem decodeHom_of (n : ℕ) (p : ℤ) :
    decodeHom n (FreeGroup.of p) = FreeGroup.of (letterOf n p) := by
  unfold decodeHom
  rw [FreeGroup.lift_apply_of]

/-- **The section of the decoding.**  The `i`-th generator is read back at the
position `i`. -/
def sectionHom (n : ℕ) : FreeGroup (Fin (n + 1)) →* FreeGroup ℤ :=
  FreeGroup.lift fun i => FreeGroup.of ((i : ℕ) : ℤ)

@[simp] theorem sectionHom_of (n : ℕ) (i : Fin (n + 1)) :
    sectionHom n (FreeGroup.of i) = FreeGroup.of ((i : ℕ) : ℤ) := by
  unfold sectionHom
  rw [FreeGroup.lift_apply_of]

theorem letterOf_natCast (n : ℕ) (i : Fin (n + 1)) :
    letterOf n ((i : ℕ) : ℤ) = i := by
  refine Fin.ext ?_
  show (((i : ℕ) : ℤ) % ((n : ℤ) + 1)).toNat = (i : ℕ)
  have hlt : ((i : ℕ) : ℤ) < (n : ℤ) + 1 := by exact_mod_cast i.isLt
  have hres : ((i : ℕ) : ℤ) % ((n : ℤ) + 1) = ((i : ℕ) : ℤ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt
  rw [hres]
  omega

/-- **The section is one.** -/
theorem decodeHom_comp_sectionHom (n : ℕ) :
    (decodeHom n).comp (sectionHom n) = MonoidHom.id (FreeGroup (Fin (n + 1))) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show decodeHom n (sectionHom n (FreeGroup.of i)) = FreeGroup.of i
  rw [sectionHom_of, decodeHom_of, letterOf_natCast]

theorem decodeHom_sectionHom (n : ℕ) (w : FreeGroup (Fin (n + 1))) :
    decodeHom n (sectionHom n w) = w :=
  congrArg (fun f : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) => f w)
    (decodeHom_comp_sectionHom n)

theorem sectionHom_injective (n : ℕ) : Function.Injective (sectionHom n) :=
  Function.LeftInverse.injective (decodeHom_sectionHom n)

/-! ## 2.  Raw words as free-group elements -/

/-- A one-letter free word. -/
theorem mk_singleton {α : Type} (y : α) (s : Bool) :
    FreeGroup.mk [(y, s)] = if s then FreeGroup.of y else (FreeGroup.of y)⁻¹ := by
  cases s
  · show FreeGroup.mk [(y, false)] = (FreeGroup.of y)⁻¹
    have h : (FreeGroup.of y)⁻¹ = FreeGroup.mk (FreeGroup.invRev [(y, true)]) :=
      FreeGroup.inv_mk
    rw [h]
    rfl
  · show FreeGroup.mk [(y, true)] = FreeGroup.of y
    rfl

theorem rawToFree_nil (n : ℕ) : rawToFree n [] = 1 := by
  show FreeGroup.mk (([] : RawWord).map fun p => (letterOfNat n p.1, p.2)) = 1
  rw [List.map_nil]
  exact FreeGroup.one_eq_mk.symm

theorem rawToFree_cons (n : ℕ) (i : ℕ) (s : Bool) (v : RawWord) :
    rawToFree n ((i, s) :: v)
      = FreeGroup.mk [(letterOfNat n i, s)] * rawToFree n v := by
  show FreeGroup.mk (((i, s) :: v).map fun p => (letterOfNat n p.1, p.2))
      = FreeGroup.mk [(letterOfNat n i, s)]
        * FreeGroup.mk (v.map fun p => (letterOfNat n p.1, p.2))
  rw [FreeGroup.mul_mk, List.map_cons]
  rfl

theorem rawToFree_append (n : ℕ) (v w : RawWord) :
    rawToFree n (v ++ w) = rawToFree n v * rawToFree n w := by
  show FreeGroup.mk ((v ++ w).map fun p => (letterOfNat n p.1, p.2))
      = FreeGroup.mk (v.map fun p => (letterOfNat n p.1, p.2))
        * FreeGroup.mk (w.map fun p => (letterOfNat n p.1, p.2))
  rw [FreeGroup.mul_mk, List.map_append]

/-- **Every element of a finite-rank free group is a raw word.** -/
theorem rawToFree_surjective (n : ℕ) : Function.Surjective (rawToFree n) := by
  intro w
  refine ⟨w.toWord.map fun p => ((p.1 : ℕ), p.2), ?_⟩
  show FreeGroup.mk (((w.toWord.map fun p => ((p.1 : ℕ), p.2))).map
      fun p => (letterOfNat n p.1, p.2)) = w
  rw [List.map_map]
  have hcomp : ((fun p : ℕ × Bool => (letterOfNat n p.1, p.2))
      ∘ (fun p : Fin (n + 1) × Bool => ((p.1 : ℕ), p.2))) = id := by
    funext p
    obtain ⟨y, t⟩ := p
    show (letterOfNat n (y : ℕ), t) = (y, t)
    have hy : letterOfNat n (y : ℕ) = y := by
      refine Fin.ext ?_
      show (y : ℕ) % (n + 1) = (y : ℕ)
      exact Nat.mod_eq_of_lt y.isLt
    rw [hy]
  rw [hcomp, List.map_id]
  exact FreeGroup.mk_toWord

/-! ## 3.  The block code of a raw word -/

/-- **The block code.**  One block of `n+1` positions per letter, the residue
inside the block naming the letter and the value carrying the sign.  The second
argument is the index of the block the word starts at. -/
noncomputable def codeSeq (n : ℕ) : RawWord → ℕ → Seq.E
  | [], _ => 0
  | (i, s) :: v, k =>
      Finsupp.single (pos n k i) (if s then (1 : ℤ) else (-1 : ℤ))
        + codeSeq n v (k + 1)

@[simp] theorem codeSeq_nil (n k : ℕ) : codeSeq n [] k = 0 := rfl

@[simp] theorem codeSeq_cons (n : ℕ) (i : ℕ) (s : Bool) (v : RawWord) (k : ℕ) :
    codeSeq n ((i, s) :: v) k
      = Finsupp.single (pos n k i) (if s then (1 : ℤ) else (-1 : ℤ))
        + codeSeq n v (k + 1) := rfl

/-- **The code of a word occupies only blocks at or above the one it starts
at.** -/
theorem codeSeq_support_lower (n : ℕ) :
    ∀ (v : RawWord) (k : ℕ), ∀ p ∈ (codeSeq n v k).support,
      (k : ℤ) * ((n : ℤ) + 1) ≤ p := by
  classical
  intro v
  induction v with
  | nil =>
      intro k p hp
      rw [codeSeq_nil] at hp
      simp at hp
  | cons x v ih =>
      obtain ⟨i, s⟩ := x
      intro k p hp
      rw [codeSeq_cons] at hp
      rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
      · have hp' : p = pos n k i := by
          have hmem := Finsupp.support_single_subset h
          simpa using hmem
        rw [hp']
        exact pos_lower n k i
      · have hle := ih (k + 1) p h
        have hcast : ((k + 1 : ℕ) : ℤ) * ((n : ℤ) + 1)
            = (k : ℤ) * ((n : ℤ) + 1) + ((n : ℤ) + 1) := by
          push_cast
          ring
        rw [hcast] at hle
        have hn : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
        linarith

/-- **The code of a word is already sorted**, so its coded product splits off
the first letter. -/
theorem elt_codeSeq_cons (n : ℕ) (i : ℕ) (s : Bool) (v : RawWord) (k : ℕ) :
    Seq.elt (codeSeq n ((i, s) :: v) k)
      = FreeGroup.of (pos n k i) ^ (if s then (1 : ℤ) else (-1 : ℤ))
        * Seq.elt (codeSeq n v (k + 1)) := by
  have hcut : ∀ p ∈ (Finsupp.single (pos n k i)
        (if s then (1 : ℤ) else (-1 : ℤ))).support,
      ∀ q ∈ (codeSeq n v (k + 1)).support, p < q := by
    intro p hp q hq
    have hp' : p = pos n k i := by
      have hmem := Finsupp.support_single_subset hp
      simpa using hmem
    have hq' : ((k + 1 : ℕ) : ℤ) * ((n : ℤ) + 1) ≤ q :=
      codeSeq_support_lower n v (k + 1) q hq
    have hcast : ((k + 1 : ℕ) : ℤ) * ((n : ℤ) + 1)
        = ((k : ℤ) + 1) * ((n : ℤ) + 1) := by
      push_cast
      ring
    rw [hcast] at hq'
    rw [hp']
    exact lt_of_lt_of_le (pos_upper n k i) hq'
  rw [codeSeq_cons, Seq.elt_add_of_lt hcut, Split.elt_single]

/-! ## 4.  The coded word decodes to the word -/

/-- The empty code is the empty product.  `Higman.Seq.elt_zero` (`BaseCases.lean`)
says the same thing; this one-line proof off `Split.elt_single` is kept so that
this file does not depend on which module of the sequence-space layer the base
cases live in. -/
theorem elt_zero_seq : Seq.elt (0 : Seq.E) = 1 := by
  have h : Seq.elt (Finsupp.single (0 : ℤ) (0 : ℤ)) = 1 := by
    rw [Split.elt_single, zpow_zero]
  rwa [Finsupp.single_zero] at h

theorem zpow_sign {G : Type} [Group G] (g : G) (s : Bool) :
    g ^ (if s then (1 : ℤ) else (-1 : ℤ)) = if s then g else g⁻¹ := by
  cases s
  · show g ^ (-1 : ℤ) = g⁻¹
    rw [zpow_neg_one]
  · show g ^ (1 : ℤ) = g
    rw [zpow_one]

/-- **Step 1 of Section 5, proved: the coded word decodes to the word.** -/
theorem decodeHom_elt_codeSeq (n : ℕ) :
    ∀ (v : RawWord) (k : ℕ),
      decodeHom n (Seq.elt (codeSeq n v k)) = rawToFree n v := by
  intro v
  induction v with
  | nil =>
      intro k
      rw [codeSeq_nil, elt_zero_seq, map_one, rawToFree_nil]
  | cons x v ih =>
      obtain ⟨i, s⟩ := x
      intro k
      rw [elt_codeSeq_cons, map_mul, map_zpow, decodeHom_of, letterOf_pos,
        ih (k + 1), zpow_sign, rawToFree_cons, mk_singleton]

/-! ## 5.  The code set of a subgroup -/

/-- The codes of the elements of `N`: the block codes of the raw words that
represent them. -/
def codeSet (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))) : Set Seq.E :=
  {f | ∃ v : RawWord, rawToFree n v ∈ N ∧ f = codeSeq n v 0}

/-- **Soundness of the code set.** -/
theorem decodeHom_mem_of_mem_codeSet (n : ℕ)
    {N : Subgroup (FreeGroup (Fin (n + 1)))} {f : Seq.E} (hf : f ∈ codeSet n N) :
    decodeHom n (Seq.elt f) ∈ N := by
  obtain ⟨v, hv, rfl⟩ := hf
  rw [decodeHom_elt_codeSeq]
  exact hv

/-- **Completeness of the code set.**  Every element of `N` is decoded from a
code in the set. -/
theorem exists_mem_codeSet (n : ℕ) {N : Subgroup (FreeGroup (Fin (n + 1)))}
    {w : FreeGroup (Fin (n + 1))} (hw : w ∈ N) :
    ∃ f ∈ codeSet n N, decodeHom n (Seq.elt f) = w := by
  obtain ⟨v, rfl⟩ := rawToFree_surjective n w
  exact ⟨codeSeq n v 0, ⟨v, hw, rfl⟩, decodeHom_elt_codeSeq n v 0⟩

/-- The subgroup of `FreeGroup ℤ` generated by the codes of `N`. -/
def codeSub (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    Subgroup (FreeGroup ℤ) :=
  Subgroup.closure (Seq.elt '' codeSet n N)

/-- The exact completion of the sorted code subgroup: add precisely the
equivalence relation forgotten by the decoder. -/
def completedCodeSub (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    Subgroup (FreeGroup ℤ) :=
  codeSub n N ⊔ MonoidHom.ker (decodeHom n)

/-- **The decoded image of the code subgroup lands in `N`.** -/
theorem map_decodeHom_codeSub_le (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    (codeSub n N).map (decodeHom n) ≤ N := by
  unfold codeSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  exact decodeHom_mem_of_mem_codeSet n hf

/-- **The kernel join is exactly the decoder preimage.**  No normality
hypothesis is needed. -/
theorem completedCodeSub_eq_comap (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    completedCodeSub n N = N.comap (decodeHom n) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      exact map_decodeHom_codeSub_le n N
        (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · intro x hx
      exact MonoidHom.mem_ker.mp hx ▸ N.one_mem
  · intro x hx
    have hdx : decodeHom n x ∈ N := Subgroup.mem_comap.mp hx
    obtain ⟨f, hf, hdecode⟩ := exists_mem_codeSet n hdx
    let c : FreeGroup ℤ := Seq.elt f
    have hc : c ∈ codeSub n N := by
      exact Subgroup.subset_closure ⟨f, hf, rfl⟩
    have hkc : sectionHom n (decodeHom n x) * c⁻¹ ∈ MonoidHom.ker (decodeHom n) := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, decodeHom_sectionHom, hdecode, inv_mul_cancel]
    have hsec : sectionHom n (decodeHom n x) ∈ completedCodeSub n N := by
      have hk' : sectionHom n (decodeHom n x) * c⁻¹ ∈ completedCodeSub n N :=
        (show MonoidHom.ker (decodeHom n) ≤ completedCodeSub n N from le_sup_right) hkc
      have hc' : c ∈ completedCodeSub n N :=
        (show codeSub n N ≤ completedCodeSub n N from le_sup_left) hc
      have hm := Subgroup.mul_mem _ hk' hc'
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
    have hkx : x * (sectionHom n (decodeHom n x))⁻¹ ∈
        MonoidHom.ker (decodeHom n) := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, decodeHom_sectionHom, mul_inv_cancel]
    have hkx' : x * (sectionHom n (decodeHom n x))⁻¹ ∈ completedCodeSub n N :=
      (show MonoidHom.ker (decodeHom n) ≤ completedCodeSub n N from le_sup_right) hkx
    have hm := Subgroup.mul_mem _ hkx' hsec
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

/-- A word belongs to `N` exactly when its canonical section belongs to the
completed code subgroup. -/
theorem sectionHom_mem_completedCodeSub_iff (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1))))
    (w : FreeGroup (Fin (n + 1))) :
    sectionHom n w ∈ completedCodeSub n N ↔ w ∈ N := by
  rw [completedCodeSub_eq_comap]
  exact decodeHom_sectionHom n w ▸ Iff.rfl

/-- The row image of the code subgroup is the subgroup generated by the row
words of the codes. -/
theorem map_rowHom_codeSub (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    (codeSub n N).map Seq.rowHom = Subgroup.closure (Seq.bElt '' codeSet n N) := by
  unfold codeSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨Seq.elt f, ⟨f, hf, rfl⟩, rfl⟩

/-- The fixed row image of the decoder kernel. -/
def periodicRowKernel (n : ℕ) : Subgroup Conj.F₃ :=
  (MonoidHom.ker (decodeHom n)).map Seq.rowHom

/-- Mapping the exact completion into the row splits it as the old code-row
subgroup joined with the fixed periodic kernel. -/
theorem map_rowHom_completedCodeSub (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    (completedCodeSub n N).map Seq.rowHom =
      Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n := by
  unfold completedCodeSub periodicRowKernel
  rw [Subgroup.map_sup, map_rowHom_codeSub]

/-! ## 6.  The two leaves -/

/-- **Leaf 1 (computability).**  The code set of a recursively enumerable normal
subgroup is recursively enumerable.

The code of a raw word is a primitive-recursive function of it ---
`Transport.codeSeq` is a fold --- and membership in the code set is the
projection of "some raw word in `N` codes to this sequence".  The work is the
normalization of a code list to the sequence it names, since a sequence has many
list representations.  `Higman.exists_primrec_of_rePred` and
`Computability.WordProblemRE.rePred_exists_eq_true` are the two ends of it.

**Nothing inhabits this structure.** -/
structure CodeRE where
  /-- Code sets of recursively enumerable subgroups are recursively enumerable. -/
  code_re : ∀ (n : ℕ) (N : Subgroup (FreeGroup (Fin (n + 1)))),
    REPred (fun v : RawWord => rawToFree n v ∈ N) → REset (codeSet n N)

/-- **Leaf 2, the content of Section 5: un-conjugation.**  Higman's Theorem 4
delivers benignness of `⟨a^{b_f} : f ∈ B⟩`; the transport needs benignness of
`⟨b_f : f ∈ B⟩`.

Nothing in the proved calculus relates the two.  The map `a^{b_f} ↦ b_f` is not
injective, so `BenignWitness.mapEmb` does not apply, and it is not the
restriction of an endomorphism of `F₃`: an endomorphism fixing `b` and `c` sends
`a^{b_f}` to `(b_f)⁻¹ φ(a) (b_f)`, and no single `φ(a)` gives `b_f` for every
`f`.  See the memo for the four refuted routes and the two that survive.

**Nothing inhabits this structure.** -/
structure UnConjugation where
  /-- Benignness passes from the conjugated code family to the code family. -/
  unconj : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
    BenignTF (Subgroup.closure (Seq.bElt '' B))

/-! ## 7.  The fixed periodic-row kernel -/

/-- Addition of one modulo `n+1`. -/
def cyclicSucc (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨((i : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- Subtraction of one modulo `n+1`. -/
def cyclicPred (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨((i : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

theorem cyclicPred_cyclicSucc (n : ℕ) (i : Fin (n + 1)) :
    cyclicPred n (cyclicSucc n i) = i := by
  apply Fin.ext
  simp only [cyclicPred, cyclicSucc, Fin.val_mk]
  omega

theorem cyclicSucc_cyclicPred (n : ℕ) (i : Fin (n + 1)) :
    cyclicSucc n (cyclicPred n i) = i := by
  apply Fin.ext
  simp only [cyclicPred, cyclicSucc, Fin.val_mk]
  omega

/-- The cyclic predecessor permutation on the decoded alphabet. -/
def cyclicPredEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := cyclicPred n
  invFun := cyclicSucc n
  left_inv := cyclicSucc_cyclicPred n
  right_inv := cyclicPred_cyclicSucc n

theorem cyclicSucc_letterOf (n : ℕ) (p : ℤ) :
    cyclicSucc n (letterOf n p) = letterOf n (p + 1) := by
  apply Fin.ext
  simp only [cyclicSucc, letterOf, Fin.val_mk]
  have hm : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hnonneg : (0 : ℤ) ≤ p % ((n : ℤ) + 1) :=
    Int.emod_nonneg p (ne_of_gt hm)
  have hlt : p % ((n : ℤ) + 1) < (n : ℤ) + 1 :=
    Int.emod_lt_of_pos p hm
  omega

theorem cyclicPred_letterOf (n : ℕ) (p : ℤ) :
    cyclicPred n (letterOf n p) = letterOf n (p - 1) := by
  apply Fin.ext
  simp only [cyclicPred, letterOf, Fin.val_mk]
  have hm : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hnonneg : (0 : ℤ) ≤ p % ((n : ℤ) + 1) :=
    Int.emod_nonneg p (ne_of_gt hm)
  have hlt : p % ((n : ℤ) + 1) < (n : ℤ) + 1 :=
    Int.emod_lt_of_pos p hm
  omega

/-- The cyclic predecessor on the finite-rank free group. -/
def cyclicPredHom (n : ℕ) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.map (cyclicPred n)

/-- The inverse cyclic successor on the finite-rank free group. -/
def cyclicSuccHom (n : ℕ) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.map (cyclicSucc n)

theorem cyclicPredHom_comp_cyclicSuccHom (n : ℕ) :
    (cyclicPredHom n).comp (cyclicSuccHom n) =
      MonoidHom.id (FreeGroup (Fin (n + 1))) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [cyclicPredHom, cyclicSuccHom, cyclicPred_cyclicSucc]

theorem cyclicSuccHom_comp_cyclicPredHom (n : ℕ) :
    (cyclicSuccHom n).comp (cyclicPredHom n) =
      MonoidHom.id (FreeGroup (Fin (n + 1))) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [cyclicPredHom, cyclicSuccHom, cyclicSucc_cyclicPred]

/-- The cyclic predecessor as a free-group automorphism. -/
def cyclicFreeEquiv (n : ℕ) :
    FreeGroup (Fin (n + 1)) ≃* FreeGroup (Fin (n + 1)) where
  toFun := cyclicPredHom n
  invFun := cyclicSuccHom n
  left_inv x := congrArg (fun f : FreeGroup (Fin (n + 1)) →*
      FreeGroup (Fin (n + 1)) => f x) (cyclicSuccHom_comp_cyclicPredHom n)
  right_inv x := congrArg (fun f : FreeGroup (Fin (n + 1)) →*
      FreeGroup (Fin (n + 1)) => f x) (cyclicPredHom_comp_cyclicSuccHom n)
  map_mul' := map_mul _

@[simp] theorem cyclicFreeEquiv_of (n : ℕ) (i : Fin (n + 1)) :
    cyclicFreeEquiv n (FreeGroup.of i) = FreeGroup.of (cyclicPred n i) := by
  simp [cyclicFreeEquiv, cyclicPredHom]

@[simp] theorem cyclicFreeEquiv_symm_of (n : ℕ) (i : Fin (n + 1)) :
    (cyclicFreeEquiv n).symm (FreeGroup.of i) = FreeGroup.of (cyclicSucc n i) := by
  simp [cyclicFreeEquiv, cyclicSuccHom]

/-- The cyclic automorphism transported to the top subgroup. -/
def cyclicTop (n : ℕ) :
    ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) ≃*
      ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) :=
  Subgroup.topEquiv.trans ((cyclicFreeEquiv n).trans Subgroup.topEquiv.symm)

@[simp] theorem coe_cyclicTop (n : ℕ)
    (x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
    ((cyclicTop n x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
      FreeGroup (Fin (n + 1))) = cyclicFreeEquiv n (x : FreeGroup (Fin (n + 1))) := rfl

@[simp] theorem coe_cyclicTop_symm (n : ℕ)
    (x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
    (((cyclicTop n).symm x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
      FreeGroup (Fin (n + 1))) =
        (cyclicFreeEquiv n).symm (x : FreeGroup (Fin (n + 1))) := rfl

/-- The finite cyclic-shift mapping torus. -/
abbrev CyclicMappingTorus (n : ℕ) : Type :=
  HNNExtension (FreeGroup (Fin (n + 1))) ⊤ ⊤ (cyclicTop n)

theorem cyclicMappingTorus_fp (n : ℕ) :
    Group.IsFinitelyPresented (CyclicMappingTorus n) := by
  letI : Group.FG ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) :=
    Group.fg_of_surjective
      (f := (Subgroup.topEquiv (G := FreeGroup (Fin (n + 1)))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := FreeGroup (Fin (n + 1)))).symm.surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (cyclicTop n)

theorem cyclicMappingTorus_torsionFree (n : ℕ) :
    IsPowerTorsionFree (CyclicMappingTorus n) :=
  HNNBritton.isPowerTorsionFree_hnn (cyclicTop n)
    IsPowerTorsionFree.of_isMulTorsionFree

/-- The rank-two detector: `b` enters the zero-th cyclic coordinate and `c`
is the stable letter. -/
def periodicHom (n : ℕ) : Row.F₀ →* CyclicMappingTorus n :=
  FreeGroup.lift fun i : Fin 2 =>
    if i = 0 then HNNExtension.of (FreeGroup.of (0 : Fin (n + 1)))
    else HNNExtension.t

@[simp] theorem periodicHom_b (n : ℕ) :
    periodicHom n Row.b = HNNExtension.of (FreeGroup.of (0 : Fin (n + 1))) := by
  simp [periodicHom, Row.b]

@[simp] theorem periodicHom_c (n : ℕ) :
    periodicHom n Row.c = HNNExtension.t := by
  simp [periodicHom, Row.c]

theorem cyclic_conj (n : ℕ) (x : FreeGroup (Fin (n + 1))) :
    (HNNExtension.t : CyclicMappingTorus n) * HNNExtension.of x *
        (HNNExtension.t : CyclicMappingTorus n)⁻¹ =
      HNNExtension.of (cyclicFreeEquiv n x) := by
  have h := HNNExtension.equiv_eq_conj (φ := cyclicTop n)
    ⟨x, Subgroup.mem_top x⟩
  rw [coe_cyclicTop] at h
  exact h.symm

theorem cyclic_conj_symm (n : ℕ) (x : FreeGroup (Fin (n + 1))) :
    (HNNExtension.t : CyclicMappingTorus n)⁻¹ * HNNExtension.of x *
        (HNNExtension.t : CyclicMappingTorus n) =
      HNNExtension.of ((cyclicFreeEquiv n).symm x) := by
  have h := HNNExtension.equiv_symm_eq_conj (φ := cyclicTop n)
    ⟨x, Subgroup.mem_top x⟩
  simpa only [coe_cyclicTop_symm] using h.symm

theorem row_succ (i : ℤ) : Row.row (i + 1) = Row.c⁻¹ * Row.row i * Row.c := by
  unfold Row.row
  simp only [zpow_neg, zpow_add, zpow_one]
  group

theorem row_pred (i : ℤ) : Row.row (i - 1) = Row.c * Row.row i * Row.c⁻¹ := by
  unfold Row.row
  simp only [zpow_neg, zpow_sub, zpow_one]
  group

/-- The periodic detector sends the `i`-th row basis element to the decoded
residue class of `i`. -/
theorem periodicHom_row (n : ℕ) (i : ℤ) :
    periodicHom n (Row.row i) = HNNExtension.of (FreeGroup.of (letterOf n i)) := by
  induction i using Int.induction_on with
  | zero =>
      rw [Row.row_zero, periodicHom_b]
      congr 2
      simpa using (letterOf_natCast n (0 : Fin (n + 1))).symm
  | succ i ih =>
      rw [row_succ, map_mul, map_mul, map_inv, periodicHom_c, ih,
        cyclic_conj_symm, cyclicFreeEquiv_symm_of, cyclicSucc_letterOf]
  | pred i ih =>
      rw [row_pred, map_mul, map_mul, map_inv, periodicHom_c, ih,
        cyclic_conj, cyclicFreeEquiv_of, cyclicPred_letterOf]

/-- The detector square commutes on the whole countable row free group. -/
theorem periodicHom_comp_basisHom (n : ℕ) :
    (periodicHom n).comp Row.basisHom =
      (HNNExtension.of : FreeGroup (Fin (n + 1)) →* CyclicMappingTorus n).comp
        (decodeHom n) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Row.basisHom_of, decodeHom_of,
    periodicHom_row]

/-- In the rank-two row carrier, the decoder kernel is the intersection of
the row kernel and the cyclic detector kernel. -/
theorem map_basisHom_ker_decodeHom (n : ℕ) :
    (MonoidHom.ker (decodeHom n)).map Row.basisHom =
      MonoidHom.ker Row.expHom ⊓ MonoidHom.ker (periodicHom n) := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Row.Row_eq_ker, ← Row.range_basisHom]
      exact ⟨w, rfl⟩
    · apply MonoidHom.mem_ker.mpr
      have hcomp := congrArg (fun f : FreeGroup ℤ →* CyclicMappingTorus n => f w)
        (periodicHom_comp_basisHom n)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hw,
        map_one] at hcomp
      exact hcomp
  · intro x hx
    rw [← Row.Row_eq_ker, ← Row.range_basisHom] at hx
    obtain ⟨w, hw⟩ := hx.1
    subst x
    refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hcomp := congrArg (fun f : FreeGroup ℤ →* CyclicMappingTorus n => f w)
      (periodicHom_comp_basisHom n)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hcomp
    have hp : periodicHom n (Row.basisHom w) = 1 := MonoidHom.mem_ker.mp hx.2
    rw [hp] at hcomp
    exact HNNExtension.of_injective (by simpa using hcomp.symm)

/-- **The periodic row kernel is benign with a torsion-free witness.** -/
theorem benignTF_periodicRowKernel (n : ℕ) : BenignTF (periodicRowKernel n) := by
  letI : Group.IsFinitelyPresented (CyclicMappingTorus n) := cyclicMappingTorus_fp n
  have hexp : BenignTF (MonoidHom.ker Row.expHom) :=
    ⟨TorsionFreeBenignWitness.ker IsPowerTorsionFree.of_isMulTorsionFree
      IsPowerTorsionFree.of_isMulTorsionFree Row.expHom⟩
  have hper : BenignTF (MonoidHom.ker (periodicHom n)) :=
    ⟨TorsionFreeBenignWitness.ker IsPowerTorsionFree.of_isMulTorsionFree
      (cyclicMappingTorus_torsionFree n) (periodicHom n)⟩
  have hint : BenignTF ((MonoidHom.ker (decodeHom n)).map Row.basisHom) := by
    rw [map_basisHom_ker_decodeHom]
    exact BenignTF.inf hexp hper
  have hmap := BenignTF.mapEmb IsPowerTorsionFree.of_isMulTorsionFree hint
    inclHom inclHom_injective
  rw [Subgroup.map_map, inclHom_comp_basisHom] at hmap
  exact hmap

/-! ## 8.  The assembly -/

/-- A free group of finite rank is a torsion-free finitely presented overgroup of
itself. -/
def freeTFOvergroup (n : ℕ) : TorsionFreeFPOvergroup (FreeGroup (Fin (n + 1))) where
  K := FreeGroup (Fin (n + 1))
  torsionFree := isPowerTorsionFree_freeGroup
  emb := MonoidHom.id _
  emb_injective := Function.injective_id

/-- The homomorphism the final `comap` runs along: read a word back at its own
positions, then spell those positions as rows of `F₃`. -/
def rowSection (n : ℕ) : FreeGroup (Fin (n + 1)) →* Conj.F₃ :=
  Seq.rowHom.comp (sectionHom n)

/-- **The preimage of the completed row subgroup is `N` exactly.** -/
theorem comap_completedRowSection_eq (n : ℕ)
    (N : Subgroup (FreeGroup (Fin (n + 1)))) :
    (Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n).comap
      (rowSection n) = N := by
  refine Subgroup.ext fun w => ?_
  rw [← map_rowHom_completedCodeSub n N]
  constructor
  · intro hw
    have hmem : Seq.rowHom (sectionHom n w) ∈
        (completedCodeSub n N).map Seq.rowHom :=
      Subgroup.mem_comap.mp hw
    rw [Subgroup.mem_map] at hmem
    obtain ⟨u, hu, hu'⟩ := hmem
    have hus : u = sectionHom n w := Seq.rowHom_injective hu'
    have hsec : sectionHom n w ∈ completedCodeSub n N := by
      rw [← hus]
      exact hu
    exact (sectionHom_mem_completedCodeSub_iff n N w).mp hsec
  · intro hw
    refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ?_)
    exact ⟨sectionHom n w,
      (sectionHom_mem_completedCodeSub_iff n N w).mpr hw, rfl⟩

/-- **Higman's Section 5, from its two leaves.**  Everything between them ---
the block coding, the decoding homomorphism and its section, the code set with
its soundness and completeness, and the final preimage --- is proved above. -/
theorem transportSectionFive_of_parts (hcode : CodeRE)
    (hunc : UnConjugation) : TransportSectionFive where
  transport := by
    intro h
    refine ⟨?_⟩
    intro n N _hN hre
    have hB : REset (codeSet n N) := hcode.code_re n N hre
    have h₁ : BenignTF (Seq.ASub (codeSet n N)) := h (codeSet n N) hB
    have h₂ : BenignTF (Subgroup.closure (Seq.bElt '' codeSet n N)) :=
      hunc.unconj (codeSet n N) h₁
    have h₃ : BenignTF
        (Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n) :=
      BenignTF.sup h₂ (benignTF_periodicRowKernel n)
    have h₄ : BenignTF ((Subgroup.closure (Seq.bElt '' codeSet n N) ⊔
        periodicRowKernel n).comap
        (rowSection n)) :=
      BenignTF.comap (freeTFOvergroup n) (rowSection n) h₃
    rw [comap_completedRowSection_eq n N] at h₄
    exact h₄

end Transport
end Higman
end GroupApproximation
