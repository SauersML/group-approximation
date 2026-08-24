import GroupApproximation.Algebra.AlternatingLampNoncommensurable
import GroupApproximation.Sofic.AlternatingLampVisibleQuotient
import GroupApproximation.Sofic.AscendingHNNWreathSofic
import GroupApproximation.Sofic.CompressionWreathFinitelyGenerated
import GroupApproximation.Sofic.FourRadicalsCoincide
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Sofic.PerfectLampCompressionRadical
import GroupApproximation.Sofic.SoficPositiveControl
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The alternating family: infinitely many groups with the same visible quotient

`Sofic/PerfectLampCompressionRadical` computes the MF radical of a compression
wreath product with a perfect torsion lamp group.  Instantiating it at
`K = Aₙ` over the concrete affine doubling datum gives, for every `n ≥ 5`, a
group

  `Wₙ = Aₙ^(V/Γ) ⋊ V`

with

  `Res_MF(Wₙ) = Rad_fd(Wₙ) = Res_fin(Wₙ) = Rad_lin(Wₙ) = Aₙ^(V/Γ)`,

so that all four approximation theories see `Wₙ` as exactly the same group `V`,
while the `Wₙ` are pairwise **noncommensurable**.  Every difference between the
members of the family therefore lies inside the part that every one of those
theories erases.

## What each ingredient contributes

* `alternating_commutator_eq_top` — `Aₙ` is perfect for `n ≥ 5`.  Mathlib has
  simplicity (`alternatingGroup.isSimpleGroup`) and nonabelianness
  (`alternatingGroup.isMulCommutative_iff_card_le_three`); a nonabelian simple
  group is perfect because its commutator subgroup is normal.
* `actualCoronaMFResidual_eq_lampRange` — the exact radical, from the
  perfect-lamp theorem plus MF-ness of the acting group.
* `four_radicals_eq_lampRange` — the four-radical collapse; finite generation
  comes from `Sofic/CompressionWreathFinitelyGenerated` and Mal'cev supplies the
  linear residual.
* `not_mulEquiv_of_ne`, `isEmpty_mulEquiv_finiteIndex_of_ne` — the separation,
  from `Algebra/AlternatingLampNoncommensurable` fed by the identification of
  the finite residual that the exact radical now supplies.
* `isSofic_alternatingWreath`, `not_isCDEOperatorMF_alternatingWreath` — each
  member is sofic and not MF.

No amalgam theorem, no Peter--Weyl, no soficity input beyond residual finiteness
of the concrete affine base.
-/

namespace GroupApproximation
namespace AlternatingLampFamily

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open MatricialStabilityRadical

/-! ## Alternating groups of degree at least five are perfect -/

/-- **`Aₙ` is perfect for `n ≥ 5`.**  The commutator subgroup is normal, so
simplicity leaves it either trivial or everything; trivial would make the group
abelian, which `Aₙ` is not once `n ≥ 4`. -/
theorem alternating_commutator_eq_top {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 5 ≤ Nat.card α) : commutator (alternatingGroup α) = ⊤ := by
  haveI := alternatingGroup.isSimpleGroup hα
  have hnormal : (commutator (alternatingGroup α)).Normal := by
    rw [commutator_def]; infer_instance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · rw [commutator_eq_bot_iff, alternatingGroup.isMulCommutative_iff_card_le_three]
      at h
    exact absurd h (by omega)
  · exact h

/-- The degree-`n` instance of the perfectness statement. -/
theorem alternating_fin_commutator_eq_top {n : ℕ} (hn : 5 ≤ n) :
    commutator (alternatingGroup (Fin n)) = ⊤ := by
  refine alternating_commutator_eq_top ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hn

/-! ## Residual finiteness, in the form the radical calculus consumes -/

/-- Mathlib's residual finiteness class gives the development's predicate. -/
theorem isResiduallyFinite_of_residuallyFinite {G : Type*} [Group G]
    [Group.ResiduallyFinite G] : IsResiduallyFinite G := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  exact Group.residuallyFinite_iff_forall_finiteIndex.mp ‹_› x
    (fun H hH => mem_finiteResidual_iff.mp hx H hH)

/-- The acting group of the concrete doubling datum, as an `IsResiduallyFinite`
statement. -/
theorem vertical_isResiduallyFinite :
    IsResiduallyFinite (Vertical conjD conjD_injective) := by
  haveI := WitnessVertical.vertical_residuallyFinite
  exact isResiduallyFinite_of_residuallyFinite

/-! ## The family -/

/-- **The degree-`n` member of the alternating family**: the `Aₙ`-lamp wreath
product over the coset space of the concrete affine doubling extension. -/
abbrev WAlt (n : ℕ) : Type :=
  WreathV (K := alternatingGroup (Fin n)) conjD conjD_injective

instance (n : ℕ) : Countable (WAlt n) := inferInstance

/-- The lamp subgroup of the degree-`n` member. -/
abbrev lampSub (n : ℕ) :
    Subgroup (WAlt n) :=
  (inl : Lamp (alternatingGroup (Fin n)) (Cosets conjD conjD_injective) →*
    WAlt n).range

/-- The base group is finitely generated: it has property `(T)`. -/
theorem gammaBar_fg : Group.FG ExplicitLinearModel.gammaBar :=
  KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT
    (G := ExplicitLinearModel.gammaBar)
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT

instance fg_WAlt (n : ℕ) : Group.FG (WAlt n) :=
  MarkedCompression.fg_wreathV conjD conjD_injective gammaBar_fg inferInstance

/-! ## The exact radical -/

/-- **The exact MF radical of the degree-`n` member.**  MF approximation forgets
the entire `Aₙ`-lamp group and remembers exactly the skeleton `V`. -/
theorem actualCoronaMFResidual_eq_lampRange {n : ℕ} (hn : 5 ≤ n) :
    actualCoronaMFResidual (WAlt n) = lampSub n :=
  PerfectLampRadical.actualCoronaMFResidual_eq_lampRange conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    (fun k => PerfectLampRadical.exists_pow_eq_one_of_finite k)
    (alternating_fin_commutator_eq_top hn)
    v1G_not_mem_range
    ((isCDEOperatorMF_iff_isOperatorMF _).mpr
      WitnessVertical.vertical_isOperatorMF)

/-- The wreath projection has kernel inside the MF radical: the containment the
radical-coincidence theorems consume. -/
theorem ker_rightHom_le_actualCoronaMFResidual {n : ℕ} (hn : 5 ≤ n) :
    (rightHom : WAlt n →* Vertical conjD conjD_injective).ker
      ≤ actualCoronaMFResidual (WAlt n) := by
  rw [ker_rightHom_eq_lampRange]
  exact PerfectLampRadical.lampRange_le_actualCoronaMFResidual conjD
    conjD_injective CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    (fun k => PerfectLampRadical.exists_pow_eq_one_of_finite k)
    (alternating_fin_commutator_eq_top hn)
    v1G_not_mem_range

/-! ## All four radicals -/

/-- **The four-radical collapse for the degree-`n` member.**  The MF radical,
the finite-dimensional unitary residual, the finite residual and the all-fields
linear residual all equal the lamp subgroup. -/
theorem four_radicals_eq_lampRange {n : ℕ} (hn : 5 ≤ n) :
    actualCoronaMFResidual (WAlt n) = lampSub n ∧
      fdUnitaryResidual (WAlt n) = lampSub n ∧
        finiteResidual (WAlt n) = lampSub n ∧
          linearResidual (WAlt n) = lampSub n := by
  obtain ⟨h1, h2, h3, h4⟩ := four_radicals_eq
    (rightHom : WAlt n →* Vertical conjD conjD_injective)
    vertical_isResiduallyFinite (ker_rightHom_le_actualCoronaMFResidual hn)
  rw [ker_rightHom_eq_lampRange] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The finite residual of the degree-`n` member is its lamp subgroup. -/
theorem finiteResidual_eq_lampRange {n : ℕ} (hn : 5 ≤ n) :
    finiteResidual (WAlt n) = lampSub n :=
  (four_radicals_eq_lampRange hn).2.2.1

/-- The finite residual, identified with the abstract lamp group. -/
noncomputable def finiteResidualEquivLamp {n : ℕ} (hn : 5 ≤ n) :
    ↥(finiteResidual (WAlt n)) ≃*
      Lamp (alternatingGroup (Fin n)) (Cosets conjD conjD_injective) :=
  (MulEquiv.subgroupCongr (finiteResidual_eq_lampRange hn)).trans
    (MonoidHom.ofInjective
      (inl_injective (N := Lamp (alternatingGroup (Fin n))
        (Cosets conjD conjD_injective)) (G := Vertical conjD conjD_injective))).symm

/-! ## The universal visible quotient -/

/-- **All members have the same MF-visible quotient.**  For every `n ≥ 5` the
universal MF-visible quotient of `Wₙ` is the acting group `V`. -/
noncomputable def universalVisibleQuotientEquiv {n : ℕ} (hn : 5 ≤ n) :
    (WAlt n ⧸ actualCoronaMFResidual (WAlt n)) ≃* Vertical conjD conjD_injective :=
  PerfectLampRadical.universalVisibleQuotientEquiv conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
    (fun k => PerfectLampRadical.exists_pow_eq_one_of_finite k)
    (alternating_fin_commutator_eq_top hn)
    v1G_not_mem_range
    ((isCDEOperatorMF_iff_isOperatorMF _).mpr
      WitnessVertical.vertical_isOperatorMF)

/-! ## Separation -/

/-- The finite residual sits inside every finite-index subgroup: it is the
intersection of them all. -/
theorem finiteResidual_le_of_finiteIndex {G : Type*} [Group G] (A : Subgroup G)
    [A.FiniteIndex] : finiteResidual G ≤ A :=
  fun _ hx => mem_finiteResidual_iff.mp hx A ‹_›

/-- **The family is pairwise non-isomorphic.** -/
theorem not_mulEquiv_of_ne {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) (hmn : m ≠ n) :
    IsEmpty (WAlt m ≃* WAlt n) :=
  not_mulEquiv_of_alternating_residual hm hn hmn
    (X := Cosets conjD conjD_injective) ⟨tSite conjD conjD_injective⟩
    ⟨finiteResidualEquivLamp hm⟩ ⟨finiteResidualEquivLamp hn⟩

/-- **The family is pairwise noncommensurable.**  No finite-index subgroup of
one member is isomorphic to a finite-index subgroup of another, even though all
members have the same universal MF-visible quotient. -/
theorem isEmpty_mulEquiv_finiteIndex_of_ne {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n)
    (hmn : m ≠ n) {A : Subgroup (WAlt m)} [A.FiniteIndex]
    {B : Subgroup (WAlt n)} [B.FiniteIndex] : IsEmpty (A ≃* B) :=
  not_mulEquiv_finiteIndex_of_alternating_residual hm hn hmn
    (X := Cosets conjD conjD_injective) ⟨tSite conjD conjD_injective⟩
    ⟨(Subgroup.subgroupOfEquivOfLe (finiteResidual_le_of_finiteIndex A)).trans
      (finiteResidualEquivLamp hm)⟩
    ⟨(Subgroup.subgroupOfEquivOfLe (finiteResidual_le_of_finiteIndex B)).trans
      (finiteResidualEquivLamp hn)⟩

/-! ## Soficity and the failure of MF -/

/-- **Every member is sofic.**  The base is residually finite, the doubling
self-embedding has finite index, and the lamp group is finite. -/
theorem isSofic_alternatingWreath (n : ℕ) : IsSofic (WAlt n) := by
  haveI := ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact AscendingHNNWreath.isSofic_wreath_cosets conjD conjD_injective
    isSofic_of_residuallyFinite (isSofic_of_finite' _)

/-- The lamp subgroup is nontrivial, so the exact radical is nontrivial. -/
theorem lampSub_ne_bot {n : ℕ} (hn : 5 ≤ n) : lampSub n ≠ ⊥ := by
  haveI : Nontrivial (alternatingGroup (Fin n)) := by
    refine alternatingGroup.nontrivial_of_three_le_card ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin n))
  intro hbot
  have hsingle : Lamp.single (tSite conjD conjD_injective) a ≠ 1 := by
    intro h
    refine ha ?_
    have hval := congrArg
      (fun f : Lamp (alternatingGroup (Fin n)) (Cosets conjD conjD_injective) =>
        f.toFun (tSite conjD conjD_injective)) h
    simpa using hval
  have hmem : (inl (Lamp.single (tSite conjD conjD_injective) a) : WAlt n)
      ∈ lampSub n := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hsingle (inl_injective (by simpa using hmem))

/-- **Every member of the family is not MF.**  The radical is the whole lamp
subgroup, which is nontrivial. -/
theorem not_isCDEOperatorMF_alternatingWreath {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsCDEOperatorMF (WAlt n) := by
  rw [isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot,
    actualCoronaMFResidual_eq_lampRange hn]
  exact lampSub_ne_bot hn

/-- **The family package.**  For every `n ≥ 5` the degree-`n` member is sofic,
not MF, finitely generated, and has exactly computable radicals, all equal to
its lamp subgroup. -/
theorem alternatingFamilyPackage {n : ℕ} (hn : 5 ≤ n) :
    IsSofic (WAlt n) ∧ ¬ IsCDEOperatorMF (WAlt n) ∧ Group.FG (WAlt n) ∧
      actualCoronaMFResidual (WAlt n) = lampSub n ∧
      fdUnitaryResidual (WAlt n) = lampSub n ∧
      finiteResidual (WAlt n) = lampSub n ∧
      linearResidual (WAlt n) = lampSub n :=
  ⟨isSofic_alternatingWreath n, not_isCDEOperatorMF_alternatingWreath hn,
    inferInstance, (four_radicals_eq_lampRange hn).1,
    (four_radicals_eq_lampRange hn).2.1, (four_radicals_eq_lampRange hn).2.2.1,
    (four_radicals_eq_lampRange hn).2.2.2⟩

end AlternatingLampFamily
end GroupApproximation
