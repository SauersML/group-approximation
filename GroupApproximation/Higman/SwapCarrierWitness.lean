import GroupApproximation.Higman.SwapCarrierFromTower

/-!
# The bespoke carrier: what it cannot be, and the one input it reduces to

`Higman.SwapCarrierFromTower` isolates route D's residual to a single
automorphism, and prices a bespoke carrier as "`Higman.Row.Lsub` with a second
stable letter implementing `τ`".  **That price was wrong, and this file proves
it wrong.**

`Higman.Row.Lsub`-style carriers, and the two-generated carrier of Higman's
base case `S`, work because their stable letters act on the coded conjugates by
*two-sided translation of the index*: `a ^ w ↦ a ^ (u w v)` for fixed `u, v`.
That is exactly the group of index maps `Higman.FlipGroup`'s `G₂` realizes ---
`Flip.conj_left` on the left, the embedding on the right --- and it is what paid
for `ρ` and for base `S`.  Section 2 proves it cannot pay for `τ`:

> `not_tau_twoSided` --- there is **no** pair `u, v ∈ K` with
> `u · b_f · v = b_{τ f}` for every `f`.

The proof is four evaluations and needs no ambient group at all: `f = 0` forces
`u v = 1`; `f = single 0 1` forces `u r₀ v = r₁`; `f = single 1 1` forces
`u r₁ v = r₀`; and then `f = oneOne`, which `τ` fixes, forces `r₁ r₀ = r₀ r₁`.

So the second stable letter cannot act by translation, and a
`Higman.Row.Lsub`-shaped construction is not merely unbuilt here, it is
excluded.  Together with `Seq.not_tau_of_endomorphism` (no endomorphism of `F₃`)
and the design constraint on `Seq.WindowApparatus` (no automorphism preserving
`emb F₃`), every mechanism this repository has ever used for a coded family is
now ruled out for `τ`.

## What is left, and it is one input

Section 3 states the only remaining shape as a single structure,
`WindowSwapper`: an element of a finitely presented torsion-free overgroup that
conjugates the *conjugator* `b_f` to `b_{τ f}` **up to an element centralizing
`a`**.  The centralizer slack is not a convenience --- section 2 is precisely
the statement that without it there is nothing to have.  `WindowSwapper` yields
`Seq.SwapWitness` outright (`WindowSwapper.toSwapWitness`), hence `τ`
(`benignTF_ASub_tauOp_of_windowSwapper`), with `transport` discharged by
`Seq.transport_of_torsionFreeImageClosure`.

This is the element form of `Seq.WindowApparatus`, and it is the form an HNN
stable letter takes, which is why it is the right target for a tower.

## Section 1 is the reusable part

`bElt_add_of_lt` and the two end-translation corollaries are the positive
calculus underneath every carrier in this lane: appending a row *above* the
support of `f` is right multiplication, appending one *below* is left
multiplication.  Base case `S` is exactly the case where both ends move by a
fixed amount, which is why that leaf was free.  `τ` moves the *middle*, and the
middle is not a translation --- that, in one sentence, is the whole difficulty.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  The end-translation calculus -/

/-- **The coding is multiplicative across a cut**, at the level of `F₃`. -/
theorem bElt_add_of_lt {u v : E} (h : ∀ i ∈ u.support, ∀ j ∈ v.support, i < j) :
    bElt (u + v) = bElt u * bElt v := by
  unfold bElt
  rw [elt_add_of_lt h, map_mul]

/-- **Appending a row above the support is right multiplication.** -/
theorem bElt_add_single_high {f : E} {j n : ℤ} (h : ∀ i ∈ f.support, i < j) :
    bElt (f + Finsupp.single j n) = bElt f * rowElt j ^ n := by
  have hord : ∀ i ∈ f.support, ∀ k ∈ (Finsupp.single j n).support, i < k := by
    intro i hi k hk
    rw [single_support_eq hk]
    exact h i hi
  rw [bElt_add_of_lt hord, bElt_single]

/-- **Appending a row below the support is left multiplication.** -/
theorem bElt_single_add_low {f : E} {j n : ℤ} (h : ∀ i ∈ f.support, j < i) :
    bElt (Finsupp.single j n + f) = rowElt j ^ n * bElt f := by
  have hord : ∀ k ∈ (Finsupp.single j n).support, ∀ i ∈ f.support, k < i := by
    intro k hk i hi
    rw [single_support_eq hk]
    exact h i hi
  rw [bElt_add_of_lt hord, bElt_single]

/-! ## 2.  The assigned shape is excluded

A second stable letter of `Higman.Row.Lsub` type acts on the coded conjugates by
a two-sided translation of the index.  No such action performs `τ`. -/

theorem tauSeq_zero_seq : tauSeq (0 : E) = 0 := by
  refine Finsupp.ext fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [tauSeq_zero, Finsupp.zero_apply, Finsupp.zero_apply]
  by_cases h1 : i = 1
  · subst h1
    rw [tauSeq_one, Finsupp.zero_apply, Finsupp.zero_apply]
  · exact tauSeq_of_ne _ i h0 h1

/-- **No two-sided translation of the index performs `τ`.**

This is the theorem that excludes the `Higman.Row.Lsub`-shaped construction.
It is stated on the conjugators, needs no ambient group, and is proved by four
evaluations: `f = 0` gives `u v = 1`, the two one-letter sequences give
`u r₀ v = r₁` and `u r₁ v = r₀`, and the two-letter witness --- which `τ` fixes
--- then forces `r₀` and `r₁` to commute. -/
theorem not_tau_twoSided (u v : F₃) :
    ¬ ∀ f : E, u * bElt f * v = bElt (tauSeq f) := by
  intro h
  have huv : u * v = 1 := by
    have h0 := h 0
    rw [tauSeq_zero_seq, bElt_zero, mul_one] at h0
    exact h0
  have hvu : v * u = 1 := by
    calc v * u = u⁻¹ * (u * v) * u := by group
      _ = u⁻¹ * 1 * u := by rw [huv]
      _ = 1 := by group
  have h01 := h (Finsupp.single (0 : ℤ) 1)
  rw [tauSeq_single_zero, bElt_single, bElt_single, zpow_one, zpow_one] at h01
  have h11 := h (Finsupp.single (1 : ℤ) 1)
  rw [tauSeq_single_one, bElt_single, bElt_single, zpow_one, zpow_one] at h11
  have hone := h oneOne
  rw [tauSeq_oneOne, bElt_oneOne] at hone
  have hcontra : rowElt 1 * rowElt 0 = rowElt 0 * rowElt 1 := by
    calc rowElt 1 * rowElt 0
        = (u * rowElt 0 * v) * (u * rowElt 1 * v) := by rw [h01, h11]
      _ = u * rowElt 0 * (v * u) * rowElt 1 * v := by group
      _ = u * (rowElt 0 * rowElt 1) * v := by rw [hvu]; group
      _ = rowElt 0 * rowElt 1 := hone
  exact rowElt_zero_one_not_commute hcontra.symm

/-- **The same, at the conjugates of `a`.**  This is the form the ambient
apparatus would consume: conjugating `a ^ (b_f)` by an element whose action on
the index is `w ↦ u w v` never lands on `a ^ (b_{τ f})`. -/
theorem not_tau_of_twoSidedConj (u v : F₃) (hu : u ∈ K) (hv : v ∈ K) :
    ¬ ∀ f : E, aElt (tauSeq f) = (u * bElt f * v)⁻¹ * a * (u * bElt f * v) := by
  intro h
  refine not_tau_twoSided u v ?_
  intro f
  have hf := h f
  unfold aElt at hf
  exact conj_a_inj
    (Subgroup.mul_mem K (Subgroup.mul_mem K hu (bElt_mem_K f)) hv)
    (bElt_mem_K (tauSeq f)) hf.symm

/-! ## 3.  The one input that is left -/

/-- **Input: a stable letter that swaps the window, modulo the centralizer of
`a`.**

The element form of `Seq.WindowApparatus`, and the form an HNN stable letter
takes.  The centralizer slack is forced: section 2 shows that an element acting
on the index by a translation cannot perform `τ`, and
`Seq.not_tau_of_endomorphism` shows no endomorphism of `F₃` can either, so the
elements `z` must be new and must lie outside `emb F₃`.

**Nothing inhabits this structure**, and it is the whole of what `τ` still
owes. -/
structure WindowSwapper where
  /-- The overgroup. -/
  K : Type
  /-- Its group structure. -/
  [group : Group K]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented K]
  /-- It is torsion-free. -/
  torsionFree : IsPowerTorsionFree K
  /-- `F₃` sits inside it. -/
  emb : F₃ →* K
  /-- ... as a subgroup. -/
  emb_injective : Function.Injective emb
  /-- The stable letter. -/
  swapper : K
  /-- It fixes `a`. -/
  swapper_a : swapper * emb a * swapper⁻¹ = emb a
  /-- It carries the conjugator of `f` to the conjugator of `τ f`, up to an
  element centralizing `a`. -/
  swapper_bElt : ∀ f : E, ∃ z : K, z * emb a = emb a * z ∧
    swapper * emb (bElt f) * swapper⁻¹ = z * emb (bElt (tauSeq f))

attribute [instance] WindowSwapper.group WindowSwapper.fp

/-- **A window swapper is Higman's swap.** -/
noncomputable def WindowSwapper.toSwapWitness (s : WindowSwapper) : SwapWitness where
  G := s.K
  torsionFree := s.torsionFree
  emb := s.emb
  emb_injective := s.emb_injective
  swap := s.swapper
  transport :=
    transport_of_torsionFreeImageClosure s.torsionFree s.emb s.emb_injective
  swap_conj := by
    intro f
    obtain ⟨z, hz, hzf⟩ := s.swapper_bElt f
    have hembf : s.emb (aElt f)
        = (s.emb (bElt f))⁻¹ * s.emb a * s.emb (bElt f) := by
      unfold aElt
      rw [map_mul, map_mul, map_inv]
    have hembt : s.emb (aElt (tauSeq f))
        = (s.emb (bElt (tauSeq f)))⁻¹ * s.emb a * s.emb (bElt (tauSeq f)) := by
      unfold aElt
      rw [map_mul, map_mul, map_inv]
    have hspread : s.swapper *
          ((s.emb (bElt f))⁻¹ * s.emb a * s.emb (bElt f)) * s.swapper⁻¹
        = (s.swapper * s.emb (bElt f) * s.swapper⁻¹)⁻¹
            * (s.swapper * s.emb a * s.swapper⁻¹)
            * (s.swapper * s.emb (bElt f) * s.swapper⁻¹) := by group
    rw [hembf, hembt, hspread, s.swapper_a, hzf]
    exact conj_of_centralizer hz

/-- **Higman's operation `τ`, from the one input that is left.** -/
theorem benignTF_ASub_tauOp_of_windowSwapper (s : WindowSwapper) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) :=
  benignTF_ASub_tauOp_of_swap s.toSwapWitness B h

end Seq
end Higman
end GroupApproximation
