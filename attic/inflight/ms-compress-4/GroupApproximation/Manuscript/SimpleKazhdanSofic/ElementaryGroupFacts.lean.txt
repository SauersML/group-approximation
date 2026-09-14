import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingGeneration
import GroupApproximation.Pestov91.Kazhdan
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import Mathlib.Topology.LocallyConstant.Algebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The elementary group of the sofic simple Kazhdan note

`simple_kazhdan_sofic_group.tex` at origin/main bf961c128, "The ring and property (T)", tex 86–100:

> Put `G = EL_3(R)` and `e_ij(r) = I_3 + r E_ij`, where `E_ij` is the usual matrix unit.  The
> elementary identities
>   `e_ij(r+s) = e_ij(r) e_ij(s)` (i ≠ j),  `[e_ik(r), e_kj(s)] = e_ij(rs)` (i, j, k distinct)
> show that the matrices `e_ij(s)`, for `s ∈ {1, u, u⁻¹} ∪ {e_a : a ∈ A}`, generate `G`.  Here
> `[g,h] = g h g⁻¹ h⁻¹`.  Ershov--Jaikin-Zapirain's theorem says that `EL_n(R)` has property (T) for
> every finitely generated unital associative ring `R` and `n ≥ 3`.  Hence `G` has property (T).  It
> is infinite because `e_12(LC(X, F_2))` is infinite.

`G = EL_3(R)` is `elementaryGroup (Fin 3) R` and `e_ij(r)` is `elementaryUnit i j h r`, with value
`1 + Matrix.single i j r`.  Mathlib's `⁅g, h⁆` is `g * h * g⁻¹ * h⁻¹`, the printed convention.  The
statements are made over every unital ring, following the printed routes.

* `PrintedElementaryIdentities`: eq:elementary.
* `PrintedElementaryGeneration`: if `gens` generates `R` as a ring, the `e_ij(s)` with
  `s ∈ gens ∪ {1}` generate `EL_3(R)`.  The printed route: the coefficients whose elementary matrices
  lie in the subgroup form a subring (`coefficientSubring`), by eq:elementary.
* `PrintedElementaryPropertyT`: a finite ring generating set makes `R` finitely generated, and
  Ershov--Jaikin-Zapirain (proved in this repository,
  `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`) gives (T).
* `PrintedElementaryInfinite`: for an infinite totally separated space `X` and a homeomorphism `T`,
  `EL_3(LC(X, F_2) ⋊_T ℤ)` is infinite, because `LC(X, F_2)` is infinite and `a ↦ e_12(a)` is
  injective.  Every infinite subshift is such a space.

The instances at the ring of the note consume the generation of `R` by `u, u⁻¹` and the letter
indicators (tex 84–86) from its owner lane.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open scoped commutatorElement

/-- Two indices of `Fin 3` leave a third. -/
theorem exists_third_index_fin_three : ∀ i j : Fin 3, ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  decide

/-! ## eq:elementary -/

/-- **eq:elementary** (tex 88–93): `e_ij(r+s) = e_ij(r) e_ij(s)` for `i ≠ j`, and
`[e_ik(r), e_kj(s)] = e_ij(rs)` for distinct `i, j, k`. -/
def PrintedElementaryIdentities : Prop :=
  ∀ (R : Type) [Ring R] (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (r s : R),
    elementaryUnit i j hij (r + s) = elementaryUnit i j hij r * elementaryUnit i j hij s ∧
      ⁅elementaryUnit i k hik r, elementaryUnit k j hkj s⁆ = elementaryUnit i j hij (r * s)

theorem printedElementaryIdentities : PrintedElementaryIdentities := by
  intro R _ i j k hij hik hkj r s
  exact ⟨(elementaryUnit_mul i j hij r s).symm, elementaryUnit_commutator i k j hik hkj hij r s⟩

/-! ## Generation -/

/-- **The coefficient subring.**  If a subgroup `H` contains every `e_ij(1)`, the coefficients `a`
with `e_ij(a) ∈ H` for all `i ≠ j` form a subring: eq:elementary gives sums, and a commutator
through a third index gives products. -/
def coefficientSubring {R : Type*} [Ring R] (H : Subgroup (Matrix (Fin 3) (Fin 3) R)ˣ)
    (hone : ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) : Subring R where
  carrier := {a | ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  mul_mem' := by
    intro a b ha hb
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (a * b) ∈ H
    intro i j h
    obtain ⟨k, hki, hkj⟩ := exists_third_index_fin_three i j
    rw [← elementaryUnit_commutator i k j (Ne.symm hki) hkj h a b, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (ha i k (Ne.symm hki)) (hb k j hkj))
      (H.inv_mem (ha i k (Ne.symm hki)))) (H.inv_mem (hb k j hkj))
  one_mem' := hone
  add_mem' := by
    intro a b ha hb
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (a + b) ∈ H
    intro i j h
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j h) (hb i j h)
  zero_mem' := by
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (0 : R) ∈ H
    intro i j h
    rw [elementaryUnit_zero]
    exact H.one_mem
  neg_mem' := by
    intro a ha
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (-a) ∈ H
    intro i j h
    have hinv : elementaryUnit i j h (-a) = (elementaryUnit i j h a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, elementaryUnit_mul, neg_add_cancel, elementaryUnit_zero]
    rw [hinv]
    exact H.inv_mem (ha i j h)

/-- **Generation** (tex 87 and 94–95): if `gens` generates `R` as a ring, the matrices `e_ij(s)` with
`s ∈ gens ∪ {1}` generate `EL_3(R)`. -/
def PrintedElementaryGeneration : Prop :=
  ∀ (R : Type) [Ring R] (gens : Set R), Subring.closure gens = ⊤ →
    elementaryGroup (Fin 3) R =
      Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ insert 1 gens ∧
        elementaryUnit i j h s = z}

theorem printedElementaryGeneration : PrintedElementaryGeneration := by
  intro R _ gens hgens
  set H : Subgroup (Matrix (Fin 3) (Fin 3) R)ˣ :=
    Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ insert 1 gens ∧
      elementaryUnit i j h s = z} with hH
  have hgen : ∀ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ insert 1 gens →
      elementaryUnit i j h s ∈ H :=
    fun i j h s hs => Subgroup.subset_closure ⟨i, j, h, s, hs, rfl⟩
  have hC : Subring.closure gens ≤
      coefficientSubring H fun i j h => hgen i j h 1 (Set.mem_insert 1 gens) :=
    Subring.closure_le.mpr fun s hs i j h => hgen i j h s (Set.mem_insert_of_mem 1 hs)
  refine le_antisymm ?_ ?_
  · show Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (a : R), elementaryUnit i j h a = z} ≤ H
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨i, j, h, a, rfl⟩
    have ha : a ∈ Subring.closure gens := by
      rw [hgens]
      exact Subring.mem_top a
    exact hC ha i j h
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, j, h, s, -, rfl⟩
    exact elementaryUnit_mem i j h s

/-- **The coefficient additive subgroup.**  The coefficients `a` with `e_ij(a) ∈ H` for all `i ≠ j`
form an additive subgroup, by the first identity of eq:elementary. -/
def coefficientAddSubgroup {R : Type*} [Ring R] (H : Subgroup (Matrix (Fin 3) (Fin 3) R)ˣ) :
    AddSubgroup R where
  carrier := {a | ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  add_mem' := by
    intro a b ha hb
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (a + b) ∈ H
    intro i j h
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j h) (hb i j h)
  zero_mem' := by
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (0 : R) ∈ H
    intro i j h
    rw [elementaryUnit_zero]
    exact H.one_mem
  neg_mem' := by
    intro a ha
    show ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (-a) ∈ H
    intro i j h
    have hinv : elementaryUnit i j h (-a) = (elementaryUnit i j h a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, elementaryUnit_mul, neg_add_cancel, elementaryUnit_zero]
    rw [hinv]
    exact H.inv_mem (ha i j h)

/-- **Generation, with `1` as a sum of generators** (at origin e80dcf20a, "The ring and property (T)"):
"So the matrices `e_ij(s)` with `s ∈ {u, u⁻¹} ∪ {e_a : a ∈ A}` generate `G`, as `1 = ∑_a e_a`."  If
`gens` generates `R` as a ring and `1` is a finite sum of elements of `gens`, the matrices `e_ij(s)` with
`s ∈ gens` generate `EL_3(R)`: their coefficients form an additive subgroup containing `gens`, hence `1`,
hence a subring. -/
def PrintedElementaryGenerationSumOne : Prop :=
  ∀ (R : Type) [Ring R] (gens : Set R), Subring.closure gens = ⊤ →
    (1 : R) ∈ AddSubmonoid.closure gens →
      elementaryGroup (Fin 3) R =
        Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ gens ∧
          elementaryUnit i j h s = z}

theorem printedElementaryGenerationSumOne : PrintedElementaryGenerationSumOne := by
  intro R _ gens hgens hone
  set H : Subgroup (Matrix (Fin 3) (Fin 3) R)ˣ :=
    Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ gens ∧
      elementaryUnit i j h s = z} with hH
  have hgen : ∀ (i j : Fin 3) (h : i ≠ j) (s : R), s ∈ gens → elementaryUnit i j h s ∈ H :=
    fun i j h s hs => Subgroup.subset_closure ⟨i, j, h, s, hs, rfl⟩
  have hadd : AddSubmonoid.closure gens ≤ (coefficientAddSubgroup H).toAddSubmonoid :=
    AddSubmonoid.closure_le.mpr fun s hs i j h => hgen i j h s hs
  have h1 : ∀ (i j : Fin 3) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H := hadd hone
  have hC : Subring.closure gens ≤ coefficientSubring H h1 :=
    Subring.closure_le.mpr fun s hs i j h => hgen i j h s hs
  refine le_antisymm ?_ ?_
  · show Subgroup.closure {z | ∃ (i j : Fin 3) (h : i ≠ j) (a : R), elementaryUnit i j h a = z} ≤ H
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨i, j, h, a, rfl⟩
    have ha : a ∈ Subring.closure gens := by
      rw [hgens]
      exact Subring.mem_top a
    exact hC ha i j h
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, j, h, s, -, rfl⟩
    exact elementaryUnit_mem i j h s

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedElementaryGenerationSumOne

/-! ## Property (T) -/

/-- **Property (T)** (tex 97–99): a finite ring generating set makes `R` finitely generated, so
`EL_3(R)` has property (T) by Ershov--Jaikin-Zapirain. -/
def PrintedElementaryPropertyT : Prop :=
  ∀ (R : Type) [Ring R] (gens : Finset R), Subring.closure (gens : Set R) = ⊤ →
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) R)

theorem printedElementaryPropertyT : PrintedElementaryPropertyT := by
  intro R _ gens hgens
  exact Pestov91.elementary_hasKazhdanPropertyT ⟨gens, hgens⟩ le_rfl

/-! ## Infiniteness -/

/-- **`LC(X, F_2)` is infinite** for an infinite totally separated space: clopen indicators
separate points, so evaluation embeds `X` into the functions on `LC(X, F_2)`. -/
theorem infinite_locallyConstant_zmodTwo (X : Type*) [TopologicalSpace X]
    [TotallySeparatedSpace X] [Infinite X] : Infinite (LocallyConstant X (ZMod 2)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : Finite (LocallyConstant X (ZMod 2)) := h
  have hinj : Function.Injective fun (x : X) (f : LocallyConstant X (ZMod 2)) => f x := by
    intro x y hxy
    by_contra hne
    obtain ⟨U, hU, hxU, hyU⟩ := exists_isClopen_of_totally_separated hne
    have h1 : LocallyConstant.charFn (ZMod 2) hU x = LocallyConstant.charFn (ZMod 2) hU y :=
      congrFun hxy _
    rw [(LocallyConstant.charFn_eq_one (ZMod 2) x hU).mpr hxU,
      (LocallyConstant.charFn_eq_zero (ZMod 2) y hU).mpr hyU] at h1
    exact one_ne_zero h1
  haveI : Finite X := Finite.of_injective _ hinj
  exact not_finite X

/-- **An infinite coefficient ring makes `EL_3` infinite**: `a ↦ e_12(φ a)` is injective. -/
theorem infinite_elementaryGroup_fin_three_of_injective {K R : Type*} [Ring K] [Infinite K]
    [Ring R] (φ : K →+* R) (hφ : Function.Injective φ) :
    Infinite ↥(elementaryGroup (Fin 3) R) := by
  refine Infinite.of_injective
    (fun a : K => (⟨elementaryUnit 0 1 (by decide) (φ a),
      elementaryUnit_mem 0 1 (by decide) (φ a)⟩ : ↥(elementaryGroup (Fin 3) R))) ?_
  intro a b hab
  have hval := congrArg (fun z : ↥(elementaryGroup (Fin 3) R) =>
    ((z : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) 0 1) hab
  simp only [elementaryUnit, Matrix.add_apply,
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide), Matrix.single_apply_same,
    zero_add] at hval
  exact hφ hval

/-- **`G` is infinite** (tex 100): for an infinite totally separated space `X` and a homeomorphism
`T`, `EL_3(LC(X, F_2) ⋊_T ℤ)` is infinite, because `e_12(LC(X, F_2))` is infinite. -/
def PrintedElementaryInfinite : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X),
    Infinite ↥(elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))

theorem printedElementaryInfinite : PrintedElementaryInfinite := by
  intro X _ _ _ T
  haveI := infinite_locallyConstant_zmodTwo X
  exact infinite_elementaryGroup_fin_three_of_injective (ClopenCrossedProduct.coeff T (ZMod 2))
    (ClopenCrossedProduct.coeff_injective T (ZMod 2))

/-! ## At `G_X` -/

/-- **"So `G` has property (T)"** (origin 9047d0d3c, "The ring and property (T)"), at `G_X = EL_3(R)`
for every subshift `X ⊆ A^ℤ` over a finite alphabet.  `R` has the finite ring generating set `u^{±1}`
and the letter indicators (`printedSubshiftRingFinitelyGenerated`), so Ershov--Jaikin-Zapirain applies
(`printedElementaryPropertyT`). -/
def PrintedGXPropertyT : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]
    (S : SymbolicDynamics.FullShift.Subshift A ℤ), HasKazhdanPropertyT.{0, 0} (G S)

theorem printedGXPropertyT : PrintedGXPropertyT := by
  intro A _ _ _ _ S
  obtain ⟨gens, hgens⟩ := printedSubshiftRingFinitelyGenerated A S
  exact printedElementaryPropertyT (R S) gens hgens

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_third_index_fin_three
#audit_axioms GroupApproximation.SimpleKazhdanSofic.infinite_locallyConstant_zmodTwo
#audit_axioms GroupApproximation.SimpleKazhdanSofic.infinite_elementaryGroup_fin_three_of_injective
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedElementaryIdentities
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedElementaryGeneration
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedElementaryPropertyT
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedElementaryInfinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGXPropertyT
