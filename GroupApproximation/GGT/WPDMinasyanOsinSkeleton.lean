import GroupApproximation.GGT.WPDAcylindricalHyperbolicity
import GroupApproximation.GroupTheory.HNNBrittonPinch
import GroupApproximation.Manuscript.NonMF.FournierFacioInput

/-!
# Minasyan--Osin's tree criterion at the manuscript's double HNN extension

`non_mf_groups_exist.tex` cites, for `E` the double HNN extension of `P` with
stable letters `u₁, u₂` and `uᵢ P uᵢ⁻¹ = Pᵢ`:

> its Bass--Serre action makes it acylindrically hyperbolic by
> Minasyan--Osin [Theorem 2.1].

**Theorem 2.1** (Minasyan--Osin, *Acylindrical hyperbolicity of groups acting on
trees*, Math. Ann. 362 (2015), 1055--1105), verbatim:

> Let `G` be a group acting minimally on a simplicial tree `T`.  Suppose that
> `G` does not fix any point of `∂T` and there exist vertices `u, v` of `T`
> such that the pointwise stabilizer `PStab_G{u,v}` is finite.  Then `G` is
> either virtually cyclic or acylindrically hyperbolic.

Their proof of it is: not virtually cyclic ⇒ (Proposition 4.8, through
Lemma 4.5 and Corollary 4.3) `G` contains a hyperbolic WPD element for the tree
action ⇒ (Theorem 3.3 = Osin's Theorem 1.2, `(AH₃) ⇒ (AH₁)`) `G` is
acylindrically hyperbolic.  **Corollary 4.3** is the step that consumes the
finite pointwise stabilizer:

> Let `G` be a group acting on a simplicial tree `T` and let `h ∈ G` be a
> hyperbolic element.  Suppose that for some vertices `u, v ∈ axis(h)`, the
> pointwise stabilizer `PStab_G({u,v})` is finite (the possibility `u = v` is
> allowed).  Then `h` satisfies the WPD condition.

## What this module contributes

The **algebraic input** of that citation, at the manuscript's `E`, proved:

* `factorOne_eq_one_of_mem_factorTwo_range` — `Δ₁ ∩ Δ₂ = 1` inside `P`, from
  injectivity of `f : P × P × S ↪ P` alone.  This is the whole reason the
  criterion applies, and it needs no hypothesis on `P`.
* `factorOne_range_ne_top` — each `Δᵢ` is a *proper* subgroup of `P` unless `P`
  is trivial.  So no `Infinite P` or finite-presentation hypothesis has to be
  added to `MinasyanOsinStatement`: see the discussion below.
* `skeleton_eq_one_of_mem_both_conjugates` — **the finite pointwise
  stabilizer**: in `E`, the two vertex stabilizers `u₁ ι(P) u₁⁻¹` and
  `u₂ ι(P) u₂⁻¹` — the stabilizers of the two vertices `u₁·x₀` and `u₂·x₀` of
  the Bass--Serre tree adjacent to the base vertex `x₀ = ι(P)` — intersect
  trivially.  This is Minasyan--Osin's `PStab_G{u,v} = 1`, in the algebraic form
  of their Remark 4.16.
* `skeletonStableLettersIndependent` and `not_isVirtuallyCyclic_skeleton` —
  `E` is **never virtually cyclic**: `u₁` and `u₂` have no common nonzero
  power, by Britton's lemma applied twice (the repository's
  `HNNBritton.t_zpow_notMem_range`).  So the virtually cyclic alternative of
  Theorem 2.1 is excluded for every `P`, `S`, `f`.

## Is `MinasyanOsinStatement` true as quantified?

`TheoremC.MinasyanOsinStatement` quantifies over **every** `P`, `S` and every
injective `f : P × P × S →* P`.  It is true as stated, and no correction is
needed:

* If `P` is trivial then `E` is the free group on `u₁, u₂`, which is
  acylindrically hyperbolic.
* If `P` is nontrivial then `Δ₁ ≠ P ≠ Δ₂` automatically
  (`factorOne_range_ne_top`): `Δ₁ = P` would force `Δ₂ ⊆ Δ₁ ∩ Δ₂ = 1`, hence
  `P ≅ Δ₂ = 1`.  So the properness hypothesis `C ≠ A ≠ D` of Minasyan--Osin's
  Corollary 2.3 — the HNN form of Theorem 2.1 — is automatic here, and so is
  the weak malnormality it also asks for, by
  `skeleton_eq_one_of_mem_both_conjugates`.
* `E` is never virtually cyclic (`not_isVirtuallyCyclic_skeleton`), so the
  first alternative of Theorem 2.1 never fires.

The one thing this module does **not** build is the Bass--Serre tree itself and
the loxodromy of `u₁u₂⁻¹` on it; that is `SkeletonAH3Input`, and
`minasyanOsinStatement_of` derives the manuscript's statement from it together
with Osin's Theorem 1.2.  The intended witness for `SkeletonAH3Input` is the
Bass--Serre tree of the one-vertex two-loop graph of groups (vertex group `P`,
both edge groups `P`, the inclusions `⊤ ↪ P` and `P ≅ Δᵢ ↪ P`), the element
`u₁u₂⁻¹` — which translates by `2` along an axis through the path
`(u₂·x₀, x₀, u₁·x₀)` — and the base vertex `x₀`.  Note that the tree action is
*not* acylindrical (the ray `x₀, u₁⁻¹·x₀, u₁⁻²·x₀, …` has pointwise stabilizer
containing `ι(P)`), which is exactly why the WPD route rather than a Sela-style
acylindricity argument is the one that closes this citation.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.Manuscript.NonMF.TheoremC
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The two `P`-factors intersect trivially -/

section Factors

variable {P S : Type} [Group P] [Group S] (f : (P × P × S) →* P)

theorem factorOne_apply (p : P) : factorOne f p = f (p, 1, 1) := rfl

theorem factorTwo_apply (q : P) : factorTwo f q = f (1, q, 1) := rfl

/-- **`Δ₁ ∩ Δ₂ = 1`.**  An element of `P` lying in both `P`-factors of the
embedded `P₁ × P₂ × S` is trivial: injectivity of `f` forces the two preimages
to agree, and the two factors of a direct product meet in the identity.  No
hypothesis on `P` is used. -/
theorem factorOne_eq_one_of_mem_factorTwo_range (hf : Function.Injective f)
    {p q : P} (h : factorOne f p = factorTwo f q) : factorOne f p = 1 := by
  have hpq : ((p, 1, 1) : P × P × S) = (1, q, 1) := by
    apply hf
    rw [← factorOne_apply, ← factorTwo_apply]
    exact h
  have hp1 : p = 1 := congrArg Prod.fst hpq
  rw [hp1, map_one]

/-- **`Δ₁` is a proper subgroup of `P` unless `P` is trivial.**  If `Δ₁` were
all of `P` then `Δ₂ ⊆ Δ₁ ∩ Δ₂ = 1`, and `Δ₂ ≅ P`.  So the properness
hypothesis of Minasyan--Osin's HNN criterion is automatic. -/
theorem factorOne_range_ne_top (hf : Function.Injective f) [Nontrivial P] :
    (factorOne f).range ≠ ⊤ := by
  intro htop
  obtain ⟨q, hq⟩ := exists_ne (1 : P)
  have hmem : factorTwo f q ∈ (factorOne f).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨p, hp⟩ := hmem
  have h1 : factorOne f p = 1 :=
    factorOne_eq_one_of_mem_factorTwo_range f hf hp
  have h2 : factorTwo f q = 1 := by rw [← hp, h1]
  exact hq (factorTwo_injective f hf (by rw [h2, map_one]))

end Factors

/-! ## The finite pointwise stabilizer in `E` -/

section Skeleton

variable {P S : Type} [Group P] [Group S] (f : (P × P × S) →* P)
    (hf : Function.Injective f)

/-- **Minasyan--Osin's `PStab_G{u,v} = 1` for `E`.**

The two vertices of the Bass--Serre tree adjacent to the base vertex
`x₀ = ι(P)` along the two stable letters have stabilizers `u₁ ι(P) u₁⁻¹` and
`u₂ ι(P) u₂⁻¹`, which are `ι(Δ₁)` and `ι(Δ₂)` by the two printed conjugation
relations.  Their intersection is `ι(Δ₁ ∩ Δ₂) = 1`.  In the algebraic form of
Minasyan--Osin's Remark 4.16 this says the pointwise stabilizer of a pair of
vertices is finite — here, trivial. -/
theorem skeleton_eq_one_of_mem_both_conjugates {z : Skeleton f hf}
    (h₁ : ∃ p : P, z = skeletonU₁ f hf * skeletonIota f hf p * (skeletonU₁ f hf)⁻¹)
    (h₂ : ∃ q : P, z = skeletonU₂ f hf * skeletonIota f hf q * (skeletonU₂ f hf)⁻¹) :
    z = 1 := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  rw [skeleton_conj_u₁] at hp
  rw [skeleton_conj_u₂] at hq
  have hiota : factorOne f p = factorTwo f q :=
    skeletonIota_injective f hf (by rw [← hp, ← hq])
  have hz1 : factorOne f p = 1 :=
    factorOne_eq_one_of_mem_factorTwo_range f hf hiota
  rw [hp, hz1, map_one]

/-! ## `E` is never virtually cyclic -/

/-- **The two stable letters have no common nonzero power.**  `u₂` is the outer
stable letter and `u₁` lies in the base copy of the outer HNN extension, so a
nonzero power of `u₂` never equals a power of `u₁` (Britton, through
`HNNBritton.t_zpow_notMem_range`); and `u₁` is the stable letter of the inner
HNN extension, so no nonzero power of it is trivial. -/
theorem skeletonStableLettersIndependent (m k : ℤ)
    (h : skeletonU₁ f hf ^ m = skeletonU₂ f hf ^ k) : m = 0 ∧ k = 0 := by
  have hu₁ : skeletonU₁ f hf ^ m =
      (HNNExtension.of :
          StageOne (factorOne f) (factorOne_injective f hf) →* Skeleton f hf)
        ((HNNExtension.t :
          StageOne (factorOne f) (factorOne_injective f hf)) ^ m) := by
    rw [map_zpow]
    rfl
  have hk : k = 0 := by
    by_contra hk0
    have hmem : ((HNNExtension.t : Skeleton f hf) ^ k) ∈
        (HNNExtension.of :
          StageOne (factorOne f) (factorOne_injective f hf) →*
            Skeleton f hf).range := by
      refine ⟨(HNNExtension.t :
        StageOne (factorOne f) (factorOne_injective f hf)) ^ m, ?_⟩
      rw [← hu₁, h]
      rfl
    exact HNNBritton.t_zpow_notMem_range _ hk0 hmem
  refine ⟨?_, hk⟩
  by_contra hm0
  have h1 : (HNNExtension.of :
      StageOne (factorOne f) (factorOne_injective f hf) →* Skeleton f hf)
      ((HNNExtension.t :
        StageOne (factorOne f) (factorOne_injective f hf)) ^ m) = 1 := by
    rw [← hu₁, h, hk, zpow_zero]
  have h2 : ((HNNExtension.t :
      StageOne (factorOne f) (factorOne_injective f hf)) ^ m) = 1 := by
    apply HNNExtension.of_injective
      (φ := stageTwoEquiv (factorOne f) (factorTwo f) (factorOne_injective f hf)
        (factorTwo_injective f hf))
    rw [h1, map_one]
  exact HNNBritton.t_zpow_ne_one
    (stageOneEquiv (factorOne f) (factorOne_injective f hf)) hm0 h2

/-- **`E` is not virtually cyclic**, for every `P`, `S` and every injective
`f`.  So the virtually cyclic alternative of Minasyan--Osin's Theorem 2.1
never fires at the manuscript's group. -/
theorem not_isVirtuallyCyclic_skeleton : ¬ IsVirtuallyCyclic (Skeleton f hf) :=
  not_isVirtuallyCyclic_of_no_common_power (skeletonStableLettersIndependent f hf)

end Skeleton

/-! ## The reduction of the manuscript's citation -/

/-- **The tree input.**  For every `P`, `S` and injective `f`, the group `E`
admits an action on a hyperbolic space with a loxodromic WPD element.

**This proposition is discharged.**  `GGT.BassSerreDoubleHNN.skeletonAH3Input`
proves it with no hypothesis, so it is not a debt and must not be recorded as
one; `minasyanOsinStatement_of` below is consumed by
`GGT.BassSerreDoubleHNN.minasyanOsinStatement_of_osin`, leaving Osin's
Theorem 1.2 as the manuscript's only remaining input for this citation.

That discharge was checked against the counterexample that refuted the general
tree criterion once stated alongside it.  In `K × ℤ` acting on a line with
leaves attached, the basepoint is a leaf: `d(x, hⁿ x) = n + 2` rather than
`n·ℓ`, so the on-axis hypothesis of the lemma actually used
(`∀ m, d(x, hᵐ x) = m·ℓ`) already excludes it, and for genuine axis pairs the
pointwise stabilizer is the infinite `K`, so its trivial-stabilizer hypothesis
fails there too.  The refuted statement differed exactly by permitting an
off-axis basepoint.  For `E` the on-axis datum holds with `ℓ = 1`.

The witness built there is the Bass--Serre tree of the *outer* HNN splitting
`E = HNN(E₁, ι(P), ι(P₂))`, whose vertices are the cosets of `E₁` — not the
one-vertex two-loop tree this module's prose first envisaged.  The two agree on
everything the argument uses: the edge stabilizers are the conjugates of `ι(P)`
either way, so `skeleton_eq_one_of_mem_both_conjugates` is the same algebra.
What changes is bookkeeping — on the coarser vertex set the axial element is
`u₂u₁⁻¹` with translation length `1` rather than `2`, though the segment
carrying the trivial pointwise stabilizer spans two edges either way.  The
outer splitting is preferable because it is Mathlib's single-letter
`HNNExtension` directly and needs no multi-letter Britton lemma — a fact about
the library rather than about the mathematics.  The two-loop picture is how
Minasyan--Osin present the construction, and it is the one the printed
sentence about `u₁ P u₁⁻¹` and `u₂ P u₂⁻¹` describes; nothing is wrong with it,
it is simply not what Mathlib ships.

`GGT.AH3Data.ofData` fixes the universe for the packaging.  The WPD field was
obtained by proving injectivity of a displacement invariant on the
`ε`-stabilizer outright, so `GGT.isWPDAt_of_pairStab_cover` and
`GGT.pairStab_zero_finite_of_trivial_intersection` are not on that path; they
remain the tools for the case where the segment stabilizer is merely finite
rather than trivial. -/
def SkeletonAH3Input : Prop :=
  ∀ (P S : Type) (_ : Group P) (_ : Group S) (f : (P × P × S) →* P)
    (hf : Function.Injective f), Nonempty (AH3Data (Skeleton f hf))

/-- **The manuscript's Minasyan--Osin citation, reduced to two inputs**: Osin's
Theorem 1.2 in the implication `(AH₃) ⇒ (AH₁)`, and the Bass--Serre tree action
of `E` with its WPD element.  Non-virtual-cyclicity, the third hypothesis of
`(AH₃)`, is proved here rather than assumed. -/
theorem minasyanOsinStatement_of (hOsin : OsinTheorem12)
    (hTree : SkeletonAH3Input) : MinasyanOsinStatement := by
  intro P S instP instS f hf
  obtain ⟨D⟩ := hTree P S instP instS f hf
  exact hOsin (Skeleton f hf) D (not_isVirtuallyCyclic_skeleton f hf)

/-- The same, with Osin's Theorem 1.2 unfolded into its two published steps:
Dahmani--Guirardel--Osin's Theorem 6.8 and Osin's `(AH₄) ⇒ (AH₁)`. -/
theorem minasyanOsinStatement_of_dgo (h68 : DGOTheorem68) (h4 : OsinAH4ToAH1)
    (hTree : SkeletonAH3Input) : MinasyanOsinStatement :=
  minasyanOsinStatement_of (osinTheorem12_of h68 h4) hTree

end GGT
end GroupApproximation
