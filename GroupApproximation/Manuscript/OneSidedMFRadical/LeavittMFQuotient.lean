import GroupApproximation.KOne.AllRanksElementary
import GroupApproximation.Leavitt.ElementaryPerfect
import GroupApproximation.Leavitt.BinaryLeavittRankTwoIso
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:leavitt-mf-quotient` at `d = 2`

`non_mf_groups_exist.tex`, Theorem `thm:leavitt-mf-quotient`:

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let
> `H = R^×`.  Then `H ≅ GL_d(R)`, and `EL_d(R) = [H,H]` is the intersection of
> the kernels of all homomorphisms from `H` to MF groups.  Moreover
> `H/EL_d(R) ≅ k^×/(k^×)^{d-1}`, the group `K₁(R)`, so every homomorphism from
> `H` to an MF group factors through `H → k^×/(k^×)^{d-1}`, and this quotient
> is MF.

This module proves the case `d = 2`, and proves it **without the literature
inputs the printed proof cites**.

## Why `d = 2` needs no Khanh--Thanh input

The printed proof reaches `H/[H,H] ≅ K₁(R) ≅ k^×/(k^×)^{d-1}` through
Khanh--Thanh's decomposition `GL_d(R) = EL_d(R) D_d(k)`.  At `d = 2` the
repository already proves the stronger statement outright:
`BinaryLeavitt.elementaryGroup_eq_top` says `GL_n(L_k(1,2)) = EL_n(L_k(1,2))`
for every field `k` and every `n ≥ 2`, which is `K₁(L_k(1,2)) = 0`.  So the
printed quotient is trivial — as the printed formula predicts, since the
exponent `d - 1` is `1` — and the decomposition and the `K₁` identification are
both consequences of a theorem already in the tree rather than citations.

The three printed subgroups therefore coincide with `H` itself:

`EL₂(R) = [H,H] = ⋂_ρ ker ρ = H`.

## What the proof spends

* `R ≅ M₂(R)` and `H ≅ GL₂(R)`: prefix self-similarity at the two-leaf comb,
  `LeavittFamily.prefixUnitsEquiv`.  This is the printed
  `x ↦ (t_i x, …)` module isomorphism, already formalized.
* `GL₂(R) = EL₂(R)`: `BinaryLeavitt.elementaryGroup_eq_top`.
* `[H,H] = H`: perfectness of `EL₄(R)` (`elementaryGroup_commutator_eq_top`,
  which needs rank `> 2`) transported to rank two along
  `RankDescent.elementaryRankTwoEquivRankFour` and then to `H`.
* Triviality of every homomorphism to an MF group: Theorem B at rank two,
  `FullDefectRankTwo.manuscriptFullComplementaryIdempotentsRankTwoFromEJZ`, at
  `s = s₀`, `t = t₀`, with the printed fullness witness `t₁(1 - s₀t₀)s₁ = 1`.

The Ershov--Jaikin-Zapirain theorem is the only hypothesis, exactly as for the
printed Theorem B over a general countable field.

## What is not proved here

The general `d ≥ 2` case is not in this module.  It needs the Khanh--Thanh
decomposition and the `K₁` identification as genuine inputs, and it needs
"a countable abelian group is MF", none of which the tree currently has.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace LeavittMFQuotient

open BinaryLeavitt

variable (k : Type) [Field k]

/-! ## `H ≅ GL₂(R)` and `GL₂(R) = EL₂(R)` -/

/-- **The printed module isomorphism**, in its unit-group form:
`R^× ≅ GL₂(R)`.  It is prefix self-similarity at the two-leaf comb, which is
the formalized version of the printed `x ↦ (t₁x, t₂x)`. -/
noncomputable def unitsEquivGL :
    (BinaryLeavittAlgebra k)ˣ ≃*
      (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ :=
  ((BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode 1)
    ((BinaryLeavitt.family k).leftCombCode_complete 1)).symm

/-- `GL₂(R) ≅ EL₂(R)`, because the two groups are equal. -/
noncomputable def glEquivElementary :
    (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ ≃*
      elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  ((MulEquiv.subgroupCongr
    (BinaryLeavitt.elementaryGroup_eq_top k 2 (by omega))).trans
      Subgroup.topEquiv).symm

/-- **`H ≅ EL₂(R)`.**  The printed `H ≅ GL_d(R)` composed with the vanishing
of `K₁`. -/
noncomputable def unitsEquivElementary :
    (BinaryLeavittAlgebra k)ˣ ≃*
      elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  (unitsEquivGL k).trans (glEquivElementary k)

/-! ## Perfectness -/

/-- `EL₂(R)` is perfect.  Perfectness of the elementary group is proved in the
tree for ranks `> 2` only; rank two is reached by transporting rank four along
the Leavitt rank equivalence. -/
theorem commutator_elementaryTwo_eq_top :
    commutator (elementaryGroup (Fin 2) (BinaryLeavittAlgebra k)) = ⊤ :=
  commutator_eq_top_of_surjective
    (RankDescent.elementaryRankTwoEquivRankFour
      (BinaryLeavitt.family k)).symm.toMonoidHom
    (RankDescent.elementaryRankTwoEquivRankFour
      (BinaryLeavitt.family k)).symm.surjective
    (elementaryGroup_commutator_eq_top 4 (by omega))

/-- **`[H,H] = H`.** -/
theorem commutator_units_eq_top :
    commutator ((BinaryLeavittAlgebra k)ˣ) = ⊤ :=
  commutator_eq_top_of_surjective (unitsEquivElementary k).symm.toMonoidHom
    (unitsEquivElementary k).symm.surjective (commutator_elementaryTwo_eq_top k)

/-! ## The printed fullness data -/

/-- The printed hypothesis of Theorem B at `R = L_k(1,2)`, with `s = s₀`,
`t = t₀` and the single fullness witness `t₁(1 - s₀t₀)s₁ = 1`. -/
theorem printedFullness :
    ∃ (m : ℕ) (a b : Fin m → BinaryLeavittAlgebra k),
      ∑ i, a i * (1 - (BinaryLeavitt.family k).s0 *
        (BinaryLeavitt.family k).t0) * b i = 1 := by
  have hp1 : (BinaryLeavitt.family k).p1
      = 1 - (BinaryLeavitt.family k).s0 * (BinaryLeavitt.family k).t0 :=
    eq_sub_of_add_eq (BinaryLeavitt.family k).p1_add_s0t0
  refine ⟨1, fun _ ↦ (BinaryLeavitt.family k).t1,
    fun _ ↦ (BinaryLeavitt.family k).s1, ?_⟩
  rw [← hp1, Fin.sum_univ_one]
  exact HilbertHotel.r1_mul_q_mul_s1 (BinaryLeavitt.family k)

/-! ## The printed theorem at `d = 2` -/

/-- **`thm:leavitt-mf-quotient` at `d = 2`, as one closed proposition.**

For every countable field `k`, with `R = L_k(1,2)` and `H = R^×`:

* `H ≅ GL₂(R)`;
* `EL₂(R) = GL₂(R)`, so the printed `K₁(R) = k^×/(k^×)^{2-1}` is trivial and
  the printed subgroup `EL_d(R)` is all of `H`;
* `[H,H] = H`; and
* every homomorphism from `H` to an MF group is trivial, so the intersection
  of all their kernels is `H` as well.

The three printed subgroups `EL_d(R)`, `[H,H]` and `⋂ρ ker ρ` therefore all
equal `H`, which is the `d = 2` reading of the printed equality, together with
the printed consequence that every homomorphism from `L_k(1,2)^×` to an MF
group is trivial. -/
def PrintedLeavittMFQuotientTwo : Prop :=
  ∀ (k : Type) [Field k] [Countable k],
    Nonempty ((BinaryLeavittAlgebra k)ˣ ≃*
        (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) ∧
      elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) = ⊤ ∧
      commutator ((BinaryLeavittAlgebra k)ˣ) = ⊤ ∧
      (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : (BinaryLeavittAlgebra k)ˣ →* M)
          (x : (BinaryLeavittAlgebra k)ˣ), f x = 1)

/-- **The theorem at `d = 2`**, with the Ershov--Jaikin-Zapirain theorem as its
only hypothesis — the same hypothesis the printed Theorem B carries over a
general countable field. -/
theorem manuscriptLeavittMFQuotientTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedLeavittMFQuotientTwo := by
  intro k _ _
  refine ⟨⟨unitsEquivGL k⟩,
    BinaryLeavitt.elementaryGroup_eq_top k 2 (by omega),
    commutator_units_eq_top k, ?_⟩
  intro M _ hM f x
  have hg := FullDefectRankTwo.manuscriptFullComplementaryIdempotentsRankTwoFromEJZ
    hEJZ (BinaryLeavittAlgebra k) (BinaryLeavitt.family k).s0
    (BinaryLeavitt.family k).t0 (BinaryLeavitt.family k).t0_s0
    (printedFullness k) 2 (by norm_num) M hM
    (f.comp (unitsEquivElementary k).symm.toMonoidHom)
    (unitsEquivElementary k x)
  simpa using hg

end LeavittMFQuotient
end OneSidedMFRadical
end Manuscript
end GroupApproximation
