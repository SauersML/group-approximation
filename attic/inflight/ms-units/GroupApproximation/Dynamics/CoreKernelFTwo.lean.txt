import GroupApproximation.Dynamics.InvolutionLocalizationStatement
import GroupApproximation.Leavitt.LocallyMatricialCongruenceKernel
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`: the `F₂` kernel clauses

`non_mf_groups_exist.tex`, proof of Lemma `lem:involution-localization` (tex 1689–1693):

> Over $\F_2$, the finite matrix argument in Theorem~\ref{thm:core-mf-radical} puts $wI_n$ in
> $\EL_n(R_X)$ for $n\ge2$; it also proves local finiteness of $K_1(I)$.

The finite matrix argument is chain-radical's generic `Leavitt/LocallyMatricialCongruenceKernel`:
for a ring hom whose kernel is locally matricial over `F₂`, the general linear restriction kernel
lies in `EL_n` for `n ≥ 2` and is locally finite.  Here it is applied to the core restriction
`R_X → R_Y`, whose kernel is the transient ideal `I`.

* `TransientIdealLocallyMatricialFTwoStatement`: the input, that `I` is locally matricial over `F₂`
  (`lem:transient-matrices`, tex 1469–1474; owner chain-matricial, planned
  `isLocallyMatricialIn_transientIdeal`).  It is stated in the shape of chain-radical's interface,
  without choosing an `F₂`-module structure on `R_X`.
* `isLocallyMatricialIn_coreTransientIdeal`: the input in the form the generic lemmas take, for
  every `F₂`-algebra structure on `R_X`.  `zmodTwoAlgebra` supplies one, since `2 = 0` in `R_X`
  over `F₂` (and any two such structures agree).
* `coreKernelElementaryStatement_of_matricial`: ct-involution's `CoreKernelElementaryStatement`,
  `K_n(I) ⊆ EL_n(R_X)` for `n ≥ 2`.
* `unitKernelLocallyFinite_of_matricial`: ct-rank-budget's `UnitKernelLocallyFiniteStatement`,
  `K_1(I)` is locally finite, through the embedding `u ↦ u I_1` of `R_X^×` in `GL_1(R_X)`.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open ChainCore.DynamicRankBudget

/-! ### `2 = 0` in `R_X` over `F₂` -/

section Algebra

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

theorem two_eq_zero_zmodTwo : (2 : ClopenCrossedProduct T (ZMod 2)) = 0 := by
  have h : ((2 : ℕ) : LocallyConstant X (ZMod 2)) = 0 := by
    ext x
    have hx : ((2 : ℕ) : LocallyConstant X (ZMod 2)) x = ((2 : ℕ) : ZMod 2) :=
      map_natCast (LocallyConstant.evalRingHom x) 2
    rw [hx]
    exact ZMod.natCast_self 2
  calc (2 : ClopenCrossedProduct T (ZMod 2))
      = coeff T (ZMod 2) ((2 : ℕ) : LocallyConstant X (ZMod 2)) := by
        rw [map_natCast]
        exact Nat.cast_ofNat.symm
    _ = 0 := by rw [h, map_zero]

theorem two_nsmul_eq_zero_zmodTwo (x : ClopenCrossedProduct T (ZMod 2)) : 2 • x = 0 := by
  rw [two_nsmul, ← two_mul, two_eq_zero_zmodTwo, zero_mul]

/-- An `F₂`-algebra structure on `R_X` over `F₂`, from `2 = 0`.  Any two `F₂`-algebra structures
on a ring agree (`Subsingleton (Algebra (ZMod 2) R)`). -/
noncomputable abbrev zmodTwoAlgebra : Algebra (ZMod 2) (ClopenCrossedProduct T (ZMod 2)) :=
  letI : Module (ZMod 2) (ClopenCrossedProduct T (ZMod 2)) :=
    AddCommGroup.zmodModule (two_nsmul_eq_zero_zmodTwo T)
  ZMod.algebraOfModule 2 (ClopenCrossedProduct T (ZMod 2))

end Algebra

/-! ### The input: `I` is locally matricial over `F₂` -/

/-- **Input, `lem:transient-matrices` (tex 1469–1474)**: over `F₂` the transient ideal `I` of
`R_X` is locally matricial.  Every finite subset of `I` lies in the range of an injective
non-unital ring hom from a finite product `∏_a M_{h_a}(F₂)`, and that range lies in `I`.  Owner
chain-matricial (planned `isLocallyMatricialIn_transientIdeal`). -/
def TransientIdealLocallyMatricialFTwoStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (F : Finset (ClopenCrossedProduct T (ZMod 2))),
    (∀ x ∈ F, x ∈ coreTransientIdeal T (ZMod 2)) →
      ∃ (m : ℕ) (h : Fin m → ℕ)
        (φ : ChainRadical.MatrixProductFTwo m h →ₙ+* ClopenCrossedProduct T (ZMod 2)),
        Function.Injective φ ∧ (∀ y, φ y ∈ coreTransientIdeal T (ZMod 2)) ∧
          ∀ x ∈ F, ∃ y, φ y = x

/-- The input in the form chain-radical's generic kernel lemmas take, for every `F₂`-algebra
structure on `R_X`: a non-unital ring hom between `F₂`-modules is `F₂`-linear. -/
theorem isLocallyMatricialIn_coreTransientIdeal (h : TransientIdealLocallyMatricialFTwoStatement)
    {X : Type} [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) [Algebra (ZMod 2) (ClopenCrossedProduct T (ZMod 2))] :
    ChainCore.IsLocallyMatricialIn (ZMod 2)
      (TwoSidedIdeal.ker (restrict T (ZMod 2) (Dynamics.image_chainRecurrentSet T)) :
        Set (ClopenCrossedProduct T (ZMod 2))) := by
  intro F hF
  obtain ⟨m, hdim, φ, hinj, hφI, hcov⟩ := h X T F hF
  refine ⟨m, hdim, { φ with map_smul' := fun c y => ?_ }, hinj, hφI, hcov⟩
  obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective c
  show φ ((r : ZMod 2) • y) = (r : ZMod 2) • φ y
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/-! ### `K_n(I) ⊆ EL_n(R_X)` for `n ≥ 2` -/

/-- **`K_n(I) ⊆ EL_n(R_X)` over `F₂` for `n ≥ 2`** (tex 1691–1693: "the finite matrix argument in
Theorem `thm:core-mf-radical` puts $wI_n$ in $\EL_n(R_X)$ for $n\ge2$").  This is ct-involution's
`CoreKernelElementaryStatement`, from the input by chain-radical's
`ker_elementaryMatrixUnitMap_le_elementaryGroup`. -/
theorem coreKernelElementaryStatement_of_matricial
    (h : TransientIdealLocallyMatricialFTwoStatement) : CoreKernelElementaryStatement := by
  intro X _ _ _ _ T n hn
  letI := zmodTwoAlgebra T
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  exact ChainRadical.ker_elementaryMatrixUnitMap_le_elementaryGroup (ι := Fin n)
    (restrict T (ZMod 2) (Dynamics.image_chainRecurrentSet T))
    (isLocallyMatricialIn_coreTransientIdeal h T)

/-! ### `K_1(I)` is locally finite -/

section UnitKernel

variable {R S : Type*} [Ring R] [Ring S]

/-- `u ↦ u I_1` embeds `R^×` in `GL_1(R)`. -/
theorem scalarUnitOne_injective :
    Function.Injective
      (Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom) := by
  intro u v huv
  apply Units.ext
  have hval : Matrix.scalar (Fin 1) (u : R) = Matrix.scalar (Fin 1) (v : R) :=
    congrArg Units.val huv
  exact (Matrix.scalar_inj (n := Fin 1)).1 hval

/-- A unit that restricts to `1` gives a scalar matrix in the general linear restriction kernel. -/
theorem scalarUnit_mem_ker_mapMatrix (f : R →+* S) (n : ℕ) (u : Rˣ) (hu : f (u : R) = 1) :
    Units.map (Matrix.scalar (Fin n) : R →+* Matrix (Fin n) (Fin n) R).toMonoidHom u ∈
      (Units.map
        (RingHom.mapMatrix f : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) S).toMonoidHom).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  show (Matrix.scalar (Fin n) (u : R)).map f = 1
  ext i j
  rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact hu
  · exact map_zero f

end UnitKernel

/-- **`K_1(I)` is locally finite over `F₂`** (tex 1693: "it also proves local finiteness of
$K_1(I)$").  This is ct-rank-budget's `UnitKernelLocallyFiniteStatement`.  `u ↦ u I_1` embeds `K_1(I)`
in the general linear restriction kernel of rank one, which is locally finite by chain-radical's
`isLocallyFiniteGroup_ker_elementaryMatrixUnitMap`. -/
theorem unitKernelLocallyFinite_of_matricial (h : TransientIdealLocallyMatricialFTwoStatement) :
    UnitKernelLocallyFiniteStatement := by
  intro X _ _ _ _ T
  letI := zmodTwoAlgebra T
  have hGL : IsLocallyFiniteGroup
      ↥(elementaryMatrixUnitMap (ι := Fin 1) (coreRestrict T (ZMod 2))).ker :=
    ChainRadical.isLocallyFiniteGroup_ker_elementaryMatrixUnitMap (coreRestrict T (ZMod 2))
      (isLocallyMatricialIn_coreTransientIdeal h T)
  let σ : ↥(unitCoreKernel T (ZMod 2)) →*
      ↥(elementaryMatrixUnitMap (ι := Fin 1) (coreRestrict T (ZMod 2))).ker :=
    ((Units.map (Matrix.scalar (Fin 1) : ClopenCrossedProduct T (ZMod 2) →+*
        Matrix (Fin 1) (Fin 1) (ClopenCrossedProduct T (ZMod 2))).toMonoidHom).comp
      (unitCoreKernel T (ZMod 2)).subtype).codRestrict _ fun u =>
      scalarUnit_mem_ker_mapMatrix (coreRestrict T (ZMod 2)) 1 u.1
        (congrArg Units.val (MonoidHom.mem_ker.1 u.2))
  refine hGL.comap σ fun u v huv => Subtype.ext ?_
  have hmap : Units.map (Matrix.scalar (Fin 1) : ClopenCrossedProduct T (ZMod 2) →+*
        Matrix (Fin 1) (Fin 1) (ClopenCrossedProduct T (ZMod 2))).toMonoidHom
        (u : (ClopenCrossedProduct T (ZMod 2))ˣ) =
      Units.map (Matrix.scalar (Fin 1) : ClopenCrossedProduct T (ZMod 2) →+*
        Matrix (Fin 1) (Fin 1) (ClopenCrossedProduct T (ZMod 2))).toMonoidHom
        (v : (ClopenCrossedProduct T (ZMod 2))ˣ) :=
    congrArg Subtype.val huv
  exact scalarUnitOne_injective hmap

end ClopenCrossedProduct
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.ClopenCrossedProduct.two_eq_zero_zmodTwo
#audit_axioms GroupApproximation.ClopenCrossedProduct.isLocallyMatricialIn_coreTransientIdeal
#audit_axioms GroupApproximation.ClopenCrossedProduct.coreKernelElementaryStatement_of_matricial
#audit_axioms GroupApproximation.ClopenCrossedProduct.scalarUnitOne_injective
#audit_axioms GroupApproximation.ClopenCrossedProduct.scalarUnit_mem_ker_mapMatrix
#audit_axioms GroupApproximation.ClopenCrossedProduct.unitKernelLocallyFinite_of_matricial
