import GroupApproximation.Dynamics.ClopenCrossedProductLaurentEval
import GroupApproximation.Dynamics.RankTwoKazhdanLimitAssembly
import GroupApproximation.Kazhdan.HaagerupFiniteProduct
import GroupApproximation.Kazhdan.GHWFiniteReduction
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.GroupTheory.Finiteness

/-!
# The restriction images at rank two are Haagerup

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1796–1805):

> Its finitely generated restriction image lies in a finite product of groups
> $\GL_2(k[z,z^{-1}])$, hence in a Haagerup group by~\cite[Theorem~4]{GHW}, and is finite.
> [...] The same reasoning applies to unit groups when every core point has period at most two:
> a finite invariant clopen partition gives matrix blocks of size at most two over $k[z,z^{-1}]$.

Let `S : Y ≃ₜ Y` and `k` a finite field.  For finitely many elements of `R_Y` take all their Laurent
coefficients, a finite set of locally constant functions, and let `Φ` record their values at `y`
(and at `S y` in the period-two case).  The fibers of `Φ` are the atoms of the finite (invariant)
clopen partition.  Elements whose coefficients are constant on these fibers form a subring
(`fiberSubring`), which contains the generators and their inverses.  Evaluating at one point of
each fiber (`evalLaurent`, resp. `evalPair`) separates this subring, so the generated subgroup
embeds in a finite product of groups `GL_2(k(z))`, and GHW Theorem 4 applies
(`Haagerup.hasHaagerupProperty_of_injective_pi_glTwo`).

* `closure_hasHaagerupProperty_glTwo_of_fixed`, `fixedCoreImageHaagerup`;
* `closure_hasHaagerupProperty_units_of_periodTwo`, `periodTwoCoreUnitImageHaagerup`;
* the endpoints over the kernel step alone: `printedFixedCoreGLTwoKazhdanFinite_of_kernel`,
  `printedPeriodTwoCoreUnitsKazhdanFinite_of_kernel`, `printedRankTwoCompressionDefectsTrivial_of_kernel`.
-/

namespace GroupApproximation
namespace ChainCore
namespace RankTwoLimit

open Haagerup ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

section FiberSubring

variable {Y : Type} [TopologicalSpace Y] (S : Y ≃ₜ Y) {k : Type} [Field k]

/-- `f` is constant on the fibers of `Φ`. -/
def FiberConst {β : Type*} (Φ : Y → β) (f : LocallyConstant Y k) : Prop :=
  ∀ y y', Φ y = Φ y' → f y = f y'

/-- Every Laurent coefficient of `x` is constant on the fibers of `Φ`. -/
def CoeffFiberConst {β : Type*} (Φ : Y → β) (x : ClopenCrossedProduct S k) : Prop :=
  ∀ g, FiberConst Φ ((ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x g))

variable {S} {β : Type*} {Φ : Y → β}

theorem coeffFiberConst_zero : CoeffFiberConst S Φ (0 : ClopenCrossedProduct S k) :=
  fun _ _ _ _ ↦ rfl

theorem coeffFiberConst_add {x x' : ClopenCrossedProduct S k} (hx : CoeffFiberConst S Φ x)
    (hx' : CoeffFiberConst S Φ x') : CoeffFiberConst S Φ (x + x') := by
  intro g y y' h
  simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, LocallyConstant.coe_add,
    Pi.add_apply]
  rw [hx g y y' h, hx' g y y' h]

theorem coeffFiberConst_neg {x : ClopenCrossedProduct S k} (hx : CoeffFiberConst S Φ x) :
    CoeffFiberConst S Φ (-x) := by
  intro g y y' h
  simp only [SkewMonoidAlgebra.coeff_neg, Finsupp.neg_apply, map_neg, LocallyConstant.coe_neg,
    Pi.neg_apply]
  rw [hx g y y' h]

theorem coeffFiberConst_sum {ι : Type*} (s : Finset ι) (f : ι → ClopenCrossedProduct S k)
    (hf : ∀ i ∈ s, CoeffFiberConst S Φ (f i)) : CoeffFiberConst S Φ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (CoeffFiberConst S Φ) (fun _ _ ha hb ↦ coeffFiberConst_add ha hb)
    coeffFiberConst_zero hf

theorem coeffFiberConst_single {c : ClopenCoeff S k} (hc : FiberConst Φ ((ClopenCoeff.of S k).symm c))
    (g : Multiplicative ℤ) : CoeffFiberConst S Φ (SkewMonoidAlgebra.single g c) := by
  classical
  intro g' y y' h
  rw [SkewMonoidAlgebra.coeff_single_apply]
  split_ifs
  · exact hc y y' h
  · rfl

theorem fiberConst_smul (hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y'))
    {c : ClopenCoeff S k} (hc : FiberConst Φ ((ClopenCoeff.of S k).symm c)) (j : Multiplicative ℤ) :
    FiberConst Φ ((ClopenCoeff.of S k).symm (j • c)) := fun y y' h ↦ by
  show (ClopenCoeff.of S k).symm c ((S ^ (-toAdd j)) y) =
    (ClopenCoeff.of S k).symm c ((S ^ (-toAdd j)) y')
  exact hc _ _ (hΦ _ y y' h)

theorem coeffFiberConst_mul (hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y'))
    {x x' : ClopenCrossedProduct S k} (hx : CoeffFiberConst S Φ x)
    (hx' : CoeffFiberConst S Φ x') : CoeffFiberConst S Φ (x * x') := by
  rw [SkewMonoidAlgebra.mul_def, SkewMonoidAlgebra.sum_def']
  refine coeffFiberConst_sum _ _ fun a _ ↦ ?_
  rw [SkewMonoidAlgebra.sum_def']
  refine coeffFiberConst_sum _ _ fun a' _ ↦ coeffFiberConst_single (fun y y' h ↦ ?_) _
  rw [map_mul, LocallyConstant.coe_mul, Pi.mul_apply, Pi.mul_apply, hx a y y' h,
    fiberConst_smul hΦ (hx' a') a y y' h]

variable (S k Φ)

/-- The elements of `R_Y` whose Laurent coefficients are constant on the fibers of `Φ`. -/
def fiberSubring (hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y')) :
    Subring (ClopenCrossedProduct S k) where
  carrier := {x | CoeffFiberConst S Φ x}
  zero_mem' := coeffFiberConst_zero
  one_mem' := coeffFiberConst_single (fun _ _ _ ↦ rfl) 1
  add_mem' := coeffFiberConst_add
  neg_mem' := coeffFiberConst_neg
  mul_mem' := coeffFiberConst_mul hΦ

end FiberSubring

/-- A coefficient of an element of `fiberSubring` that vanishes at one point of every fiber
vanishes. -/
theorem eq_zero_of_fiberSubring {Y : Type} [TopologicalSpace Y] {S : Y ≃ₜ Y} {k : Type} [Field k]
    {β : Type*} {Φ : Y → β} {hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y')}
    {x : ClopenCrossedProduct S k} (hx : x ∈ fiberSubring S k Φ hΦ) (rep : Set.range Φ → Y)
    (hrep : ∀ a, Φ (rep a) = a)
    (h0 : ∀ (a : Set.range Φ) (n : ℤ), (ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x (ofAdd n)) (rep a) = 0) :
    x = 0 := by
  refine SkewMonoidAlgebra.ext fun g ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ofAdd n = g := ⟨toAdd g, rfl⟩
  apply (ClopenCoeff.of S k).symm.injective
  refine LocallyConstant.ext fun y ↦ ?_
  have h4 := hx (ofAdd n) (rep ⟨Φ y, y, rfl⟩) y (hrep _)
  rw [← h4, h0]
  rfl

section Fixed

variable {Y : Type} [TopologicalSpace Y] (S : Y ≃ₜ Y) (k : Type) [Field k] [Finite k]

/-- **Fixed core (tex 1796–1798).**  A finitely generated subgroup of `GL_2(R_Y)`, `S = id`, has the
Haagerup property. -/
theorem closure_hasHaagerupProperty_glTwo_of_fixed (hS : ∀ y, S y = y)
    (t : Set (GL (Fin 2) (ClopenCrossedProduct S k))) (ht : t.Finite) :
    HasHaagerupProperty.{0, 0} (Subgroup.closure t) := by
  classical
  let E : Finset (ClopenCrossedProduct S k) :=
    ht.toFinset.biUnion fun g ↦ Finset.univ.image fun p : Fin 2 × Fin 2 × Bool ↦
      if p.2.2 then (g : Matrix (Fin 2) (Fin 2) (ClopenCrossedProduct S k)) p.1 p.2.1
      else (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (ClopenCrossedProduct S k)) p.1 p.2.1
  let C : Finset (LocallyConstant Y k) :=
    E.biUnion fun x ↦ (SkewMonoidAlgebra.support x).image fun g ↦ (ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x g)
  let Φ : Y → C → k := fun y c ↦ (c : LocallyConstant Y k) y
  have hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y') := by
    intro n y y' h
    rwa [zpow_apply_of_apply_eq (hS y) n, zpow_apply_of_apply_eq (hS y') n]
  let A := fiberSubring S k Φ hΦ
  have hE : ∀ x ∈ E, x ∈ A := by
    intro x hx g y y' hyy'
    by_cases hg : g ∈ SkewMonoidAlgebra.support x
    · have hc : (ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x g) ∈ C :=
        Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
      exact congrFun hyy' ⟨_, hc⟩
    · rw [SkewMonoidAlgebra.notMem_support_iff.mp hg]
      rfl
  let H : Subgroup (GL (Fin 2) (ClopenCrossedProduct S k)) :=
    { carrier := {g | ∀ i j, (g : Matrix (Fin 2) (Fin 2) (ClopenCrossedProduct S k)) i j ∈ A ∧
        (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (ClopenCrossedProduct S k)) i j ∈ A}
      one_mem' := fun i j ↦ by
        simp only [inv_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> exact ⟨by simp [A.one_mem, A.zero_mem], by simp [A.one_mem, A.zero_mem]⟩
      mul_mem' := fun {a b} ha hb i j ↦ by
        simp only [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact ⟨A.sum_mem fun l _ ↦ A.mul_mem (ha i l).1 (hb l j).1,
          A.sum_mem fun l _ ↦ A.mul_mem (hb i l).2 (ha l j).2⟩
      inv_mem' := fun {a} ha i j ↦ by
        simp only [inv_inv]
        exact ⟨(ha i j).2, (ha i j).1⟩ }
  have hle : Subgroup.closure t ≤ H := (Subgroup.closure_le H).mpr fun g hg i j ↦
    ⟨hE _ (Finset.mem_biUnion.mpr ⟨g, ht.mem_toFinset.mpr hg,
        Finset.mem_image.mpr ⟨(i, j, true), Finset.mem_univ _, by simp⟩⟩),
      hE _ (Finset.mem_biUnion.mpr ⟨g, ht.mem_toFinset.mpr hg,
        Finset.mem_image.mpr ⟨(i, j, false), Finset.mem_univ _, by simp⟩⟩)⟩
  haveI : Finite (Set.range Φ) := Subtype.finite
  let rep : Set.range Φ → Y := fun a ↦ a.2.choose
  have hrep : ∀ a, Φ (rep a) = a := fun a ↦ a.2.choose_spec
  haveI : Finite t := ht.to_subtype
  haveI : Countable (Subgroup.closure t) :=
    Manuscript.OneSidedMFRadical.JacobsonRankTwo.countable_of_groupFG (Group.closure_finite_fg t)
  let K := FractionRing (LaurentPolynomial k)
  let f : ∀ a : Set.range Φ, Subgroup.closure t →* GL (Fin 2) K := fun a ↦
    (glMap (Fin 2) ((algebraMap (LaurentPolynomial k) K).comp
      (evalLaurent S k (hS (rep a))))).comp (Subgroup.closure t).subtype
  refine hasHaagerupProperty_of_injective_pi_glTwo f fun γ δ hγδ ↦ ?_
  have hγ := hle γ.2
  have hδ := hle δ.2
  refine Subtype.ext (Units.ext (Matrix.ext fun i j ↦ ?_))
  rw [← sub_eq_zero]
  refine eq_zero_of_fiberSubring (A.sub_mem (hγ i j).1 (hδ i j).1) rep hrep fun a n ↦ ?_
  have h1 : algebraMap (LaurentPolynomial k) K (evalLaurent S k (hS (rep a))
        (((γ : GL (Fin 2) (ClopenCrossedProduct S k)) : Matrix (Fin 2) (Fin 2) _) i j)) =
      algebraMap (LaurentPolynomial k) K (evalLaurent S k (hS (rep a))
        (((δ : GL (Fin 2) (ClopenCrossedProduct S k)) : Matrix (Fin 2) (Fin 2) _) i j)) :=
    congrArg (fun z : GL (Fin 2) K ↦ (z : Matrix (Fin 2) (Fin 2) K) i j) (hγδ a)
  have h2 := IsFractionRing.injective (LaurentPolynomial k) K h1
  have h3 := coeff_evalLaurent S k (hS (rep a))
    ((((γ : GL (Fin 2) (ClopenCrossedProduct S k)) : Matrix (Fin 2) (Fin 2) _) i j) -
      (((δ : GL (Fin 2) (ClopenCrossedProduct S k)) : Matrix (Fin 2) (Fin 2) _) i j)) n
  rw [map_sub, h2, sub_self] at h3
  rw [← h3]
  rfl

/-- **Printed step (tex 1796–1798), closed.** -/
theorem fixedCoreImageHaagerup : FixedCoreImageHaagerupStatement := by
  intro Y _ S k _ _ hS M hM
  exact GHW.hasHaagerupProperty_of_closure_finite M fun t ht ↦
    closure_hasHaagerupProperty_glTwo_of_fixed S k hS t ht

end Fixed

section PeriodTwo

variable {Y : Type} [TopologicalSpace Y] (S : Y ≃ₜ Y) (k : Type) [Field k] [Finite k]

/-- **Core periods at most two (tex 1802–1805).**  A finitely generated subgroup of `R_Y^×`, when
`S ∘ S = id`, has the Haagerup property. -/
theorem closure_hasHaagerupProperty_units_of_periodTwo (hS : ∀ y, S (S y) = y)
    (t : Set (ClopenCrossedProduct S k)ˣ) (ht : t.Finite) :
    HasHaagerupProperty.{0, 0} (Subgroup.closure t) := by
  classical
  let E : Finset (ClopenCrossedProduct S k) :=
    ht.toFinset.biUnion fun u ↦ {(u : ClopenCrossedProduct S k), (↑u⁻¹ : ClopenCrossedProduct S k)}
  let C : Finset (LocallyConstant Y k) :=
    E.biUnion fun x ↦ (SkewMonoidAlgebra.support x).image fun g ↦ (ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x g)
  let Φ : Y → C → k × k := fun y c ↦ ((c : LocallyConstant Y k) y, (c : LocallyConstant Y k) (S y))
  have hΦ : ∀ (n : ℤ) y y', Φ y = Φ y' → Φ ((S ^ n) y) = Φ ((S ^ n) y') := by
    intro n y y' h
    rw [zpow_apply_of_apply_apply_eq hS, zpow_apply_of_apply_apply_eq hS]
    by_cases hn : Even n
    · simpa only [hn, ↓reduceIte] using h
    · simp only [hn, ↓reduceIte]
      funext c
      have hc := congrFun h c
      simp only [Φ, Prod.mk.injEq, hS] at hc ⊢
      exact ⟨hc.2, hc.1⟩
  let A := fiberSubring S k Φ hΦ
  have hE : ∀ x ∈ E, x ∈ A := by
    intro x hx g y y' hyy'
    by_cases hg : g ∈ SkewMonoidAlgebra.support x
    · have hc : (ClopenCoeff.of S k).symm (SkewMonoidAlgebra.coeff x g) ∈ C :=
        Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩
      exact congrArg Prod.fst (congrFun hyy' ⟨_, hc⟩)
    · rw [SkewMonoidAlgebra.notMem_support_iff.mp hg]
      rfl
  let H : Subgroup (ClopenCrossedProduct S k)ˣ :=
    { carrier := {u | (u : ClopenCrossedProduct S k) ∈ A ∧ (↑u⁻¹ : ClopenCrossedProduct S k) ∈ A}
      one_mem' := by
        show ((1 : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A ∧
          ((1⁻¹ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A
        rw [inv_one, Units.val_one]
        exact ⟨A.one_mem, A.one_mem⟩
      mul_mem' := fun {a b} ha hb ↦ by
        show ((a * b : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A ∧
          (((a * b)⁻¹ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A
        rw [mul_inv_rev, Units.val_mul, Units.val_mul]
        exact ⟨A.mul_mem ha.1 hb.1, A.mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha ↦ by
        show ((a⁻¹ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A ∧
          ((a⁻¹⁻¹ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) ∈ A
        rw [inv_inv]
        exact ⟨ha.2, ha.1⟩ }
  have hle : Subgroup.closure t ≤ H := (Subgroup.closure_le H).mpr fun u hu ↦
    ⟨hE _ (Finset.mem_biUnion.mpr ⟨u, ht.mem_toFinset.mpr hu, by simp⟩),
      hE _ (Finset.mem_biUnion.mpr ⟨u, ht.mem_toFinset.mpr hu, by simp⟩)⟩
  haveI : Finite (Set.range Φ) := Subtype.finite
  let rep : Set.range Φ → Y := fun a ↦ a.2.choose
  have hrep : ∀ a, Φ (rep a) = a := fun a ↦ a.2.choose_spec
  haveI : Finite t := ht.to_subtype
  haveI : Countable (Subgroup.closure t) :=
    Manuscript.OneSidedMFRadical.JacobsonRankTwo.countable_of_groupFG (Group.closure_finite_fg t)
  let K := FractionRing (LaurentPolynomial k)
  let f : ∀ a : Set.range Φ, Subgroup.closure t →* GL (Fin 2) K := fun a ↦
    (Units.map (((RingHom.mapMatrix (algebraMap (LaurentPolynomial k) K)).comp
      (evalPair S k hS (rep a)) : ClopenCrossedProduct S k →+* Matrix (Fin 2) (Fin 2) K) :
        ClopenCrossedProduct S k →* Matrix (Fin 2) (Fin 2) K)).comp (Subgroup.closure t).subtype
  refine hasHaagerupProperty_of_injective_pi_glTwo f fun γ δ hγδ ↦ ?_
  have hγ := hle γ.2
  have hδ := hle δ.2
  refine Subtype.ext (Units.ext ?_)
  rw [← sub_eq_zero]
  refine eq_zero_of_fiberSubring (A.sub_mem hγ.1 hδ.1) rep hrep fun a n ↦ ?_
  have hentry : ∀ l : Fin 2, evalPair S k hS (rep a) ((γ : (ClopenCrossedProduct S k)ˣ) :
      ClopenCrossedProduct S k) 0 l =
      evalPair S k hS (rep a) ((δ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) 0 l := by
    intro l
    have h1 : algebraMap (LaurentPolynomial k) K (evalPair S k hS (rep a)
          ((γ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) 0 l) =
        algebraMap (LaurentPolynomial k) K (evalPair S k hS (rep a)
          ((δ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) 0 l) :=
      congrArg (fun z : GL (Fin 2) K ↦ (z : Matrix (Fin 2) (Fin 2) K) 0 l) (hγδ a)
    exact IsFractionRing.injective (LaurentPolynomial k) K h1
  have h3 := coeff_evalPair_row S k hS (rep a)
    (((γ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) -
      ((δ : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k)) n
  rw [map_sub, Matrix.sub_apply, Matrix.sub_apply, hentry 0, hentry 1, sub_self, sub_self,
    add_zero] at h3
  rw [← h3]
  rfl

/-- **Printed step (tex 1802–1805), closed.** -/
theorem periodTwoCoreUnitImageHaagerup : PeriodTwoCoreUnitImageHaagerupStatement := by
  intro Y _ S k _ _ hS M hM
  exact GHW.hasHaagerupProperty_of_closure_finite M fun t ht ↦
    closure_hasHaagerupProperty_units_of_periodTwo S k hS t ht

end PeriodTwo

/-- **Printed (tex 1795–1800)**, over the remaining-kernel step alone. -/
theorem printedFixedCoreGLTwoKazhdanFinite_of_kernel
    (hker : CoreRestrictionLocallyFiniteKernelStatement) : PrintedFixedCoreGLTwoKazhdanFinite :=
  printedFixedCoreGLTwoKazhdanFinite_of_steps hker fixedCoreImageHaagerup

/-- **Printed (tex 1802–1805)**, over the remaining-kernel step alone. -/
theorem printedPeriodTwoCoreUnitsKazhdanFinite_of_kernel
    (hker : CoreRestrictionLocallyFiniteKernelStatement) :
    PrintedPeriodTwoCoreUnitsKazhdanFinite :=
  printedPeriodTwoCoreUnitsKazhdanFinite_of_steps hker periodTwoCoreUnitImageHaagerup

/-- **Printed (tex 1801–1802)**, over the remaining-kernel step alone. -/
theorem printedRankTwoCompressionDefectsTrivial_of_kernel
    (hker : CoreRestrictionLocallyFiniteKernelStatement) :
    PrintedRankTwoCompressionDefectsTrivial :=
  printedRankTwoCompressionDefectsTrivial_of_steps hker fixedCoreImageHaagerup
    periodTwoCoreUnitImageHaagerup

end RankTwoLimit
end ChainCore
end GroupApproximation

#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.fixedCoreImageHaagerup
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.periodTwoCoreUnitImageHaagerup
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedFixedCoreGLTwoKazhdanFinite_of_kernel
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedPeriodTwoCoreUnitsKazhdanFinite_of_kernel
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedRankTwoCompressionDefectsTrivial_of_kernel
