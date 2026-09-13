import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Invertible matrices over a finite product of matrix algebras over `F_2`

`non_mf_groups_exist.tex`, proof of `thm:core-mf-radical`:

> For $n\ge2$,
> $\GL_n(B)=\EL_n(B)\cong\prod_a\mathrm{SL}_{nh_a}(\F_2)$.
> Indeed every invertible matrix over $\F_2$ has determinant one.
> Under block flattening, scalar roots across distinct outer blocks
> are block roots; a scalar root within one block is a commutator
> through another block.

Here `B = MatrixProductFTwo m h = ∏_{a < m} M_{h_a}(F_2)`, and `GL_n(B) = EL_n(B)` is the
statement `elementaryGroup (Fin n) B = ⊤`.

* `elementaryGroup_matrix_zmodTwo_eq_top`: `GL_n(M_κ(F_2)) = EL_n(M_κ(F_2))` for `n ≥ 2`.  Block
  flattening `elementaryBlockGroup_map` carries the two block-root sentences, and
  `FinitaryLinear.elementaryGroup_zmodTwo_eq_top` is `GL_N(F_2) = EL_N(F_2)`.
* `elementaryGroup_pi_eq_top`: `EL_n` of a finite product is everything when every factor is.
  The coordinate map `unitsMatrixPiHom : GL_n(∏_a A_a) →* ∏_a GL_n(A_a)` is injective, and the
  coordinates of the root `x_{ij}(r e_a)` are the root `x_{ij}(r)` at `a` and `1` elsewhere
  (`unitsMatrixPiHom_elementaryUnit`); so it is onto (`unitsMatrixPiEquiv`).
* `elementaryGroup_matrixProductFTwo_eq_top`: `GL_n(B) = EL_n(B)`.
* `det_units_zmodTwo`: every invertible matrix over `F_2` has determinant one, so
  `GL_N(F_2) ≃* SL_N(F_2)` (`unitsZModTwoEquivSL`).
* `elementaryMatrixProductFTwoEquiv`: `EL_n(B) ≃* ∏_a SL_{n h_a}(F_2)`, the index set of the
  `a`-th factor being `ι × Fin (h a)`, of cardinality `n h_a`.
-/

namespace GroupApproximation
namespace ChainRadical

open Matrix

/-- The finite matrix-product algebra `B = ∏_{a < m} M_{h_a}(F_2)`. -/
abbrev MatrixProductFTwo (m : ℕ) (h : Fin m → ℕ) : Type :=
  ∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) (ZMod 2)

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`GL_n(M_κ(F_2)) = EL_n(M_κ(F_2))` for `n ≥ 2`**, by block flattening. -/
theorem elementaryGroup_matrix_zmodTwo_eq_top [Nontrivial ι] (κ : Type*) [Fintype κ]
    [DecidableEq κ] : elementaryGroup ι (Matrix κ κ (ZMod 2)) = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ?_
  have hmem : elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := ZMod 2) u ∈
      (elementaryGroup ι (Matrix κ κ (ZMod 2))).map
        (elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := ZMod 2)).toMonoidHom := by
    rw [elementaryBlockGroup_map, FinitaryLinear.elementaryGroup_zmodTwo_eq_top (ι × κ)]
    exact Subgroup.mem_top _
  obtain ⟨v, hv, hvu⟩ := hmem
  have hvu' : v = u := (elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := ZMod 2)).injective hvu
  rw [← hvu']
  exact hv

end Block

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {A : α → Type*} [∀ a, Ring (A a)]

/-- The coordinate projections `GL_n(∏_a A_a) →* ∏_a GL_n(A_a)`. -/
def unitsMatrixPiHom : (Matrix ι ι (∀ a, A a))ˣ →* ∀ a, (Matrix ι ι (A a))ˣ :=
  MonoidHom.pi fun a ↦ elementaryMatrixUnitMap (Pi.evalRingHom A a)

/-- A matrix over a product ring is determined by its coordinates. -/
theorem unitsMatrixPiHom_injective :
    Function.Injective (unitsMatrixPiHom (ι := ι) (A := A)) := by
  intro u v huv
  refine Units.ext (Matrix.ext fun k l ↦ funext fun a ↦ ?_)
  exact congrArg
    (fun w : ∀ a, (Matrix ι ι (A a))ˣ ↦ ((w a : (Matrix ι ι (A a))ˣ) : Matrix ι ι (A a)) k l) huv

theorem unitsMatrixPiHom_elementaryUnit_self [DecidableEq α] (i j : ι) (hij : i ≠ j) (a : α)
    (r : A a) :
    unitsMatrixPiHom (ι := ι) (A := A) (elementaryUnit i j hij (Pi.single a r)) a =
      elementaryUnit i j hij r := by
  change elementaryMatrixUnitMap (Pi.evalRingHom A a) (elementaryUnit i j hij (Pi.single a r)) = _
  rw [elementaryMatrixUnitMap_elementaryUnit]
  change elementaryUnit i j hij (Pi.single a r a) = _
  rw [Pi.single_eq_same]

theorem unitsMatrixPiHom_elementaryUnit_of_ne [DecidableEq α] (i j : ι) (hij : i ≠ j) {a b : α}
    (hb : b ≠ a) (r : A a) :
    unitsMatrixPiHom (ι := ι) (A := A) (elementaryUnit i j hij (Pi.single a r)) b = 1 := by
  change elementaryMatrixUnitMap (Pi.evalRingHom A b) (elementaryUnit i j hij (Pi.single a r)) = _
  rw [elementaryMatrixUnitMap_elementaryUnit]
  change elementaryUnit i j hij (Pi.single a r b) = _
  rw [Pi.single_eq_of_ne hb, elementaryUnit_zero]

/-- The coordinates of the root `x_{ij}(r e_a)` are `x_{ij}(r)` at `a` and `1` elsewhere. -/
theorem unitsMatrixPiHom_elementaryUnit [DecidableEq α] (i j : ι) (hij : i ≠ j) (a : α)
    (r : A a) :
    unitsMatrixPiHom (ι := ι) (A := A) (elementaryUnit i j hij (Pi.single a r)) =
      Pi.mulSingle a (elementaryUnit i j hij r) := by
  funext b
  rcases eq_or_ne b a with rfl | hb
  · rw [Pi.mulSingle_eq_same, unitsMatrixPiHom_elementaryUnit_self]
  · rw [Pi.mulSingle_eq_of_ne hb, unitsMatrixPiHom_elementaryUnit_of_ne i j hij hb]

/-- If every factor has `GL_n = EL_n`, every tuple of invertible matrices is the coordinate
tuple of an elementary matrix over the product. -/
theorem top_le_map_unitsMatrixPiHom [Fintype α] [DecidableEq α]
    (hA : ∀ a, elementaryGroup ι (A a) = ⊤) :
    ⊤ ≤ (elementaryGroup ι (∀ a, A a)).map (unitsMatrixPiHom (ι := ι) (A := A)) := by
  have hle : Subgroup.pi Set.univ (fun a ↦ (⊤ : Subgroup (Matrix ι ι (A a))ˣ)) ≤
      (elementaryGroup ι (∀ a, A a)).map (unitsMatrixPiHom (ι := ι) (A := A)) := by
    refine Subgroup.pi_le_iff.2 fun a ↦ Subgroup.map_le_iff_le_comap.2 ?_
    refine (hA a).symm.trans_le ((Subgroup.closure_le (K := _)).2 ?_)
    rintro _ ⟨i, j, hij, r, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_map.2
      ⟨_, elementaryUnit_mem i j hij (Pi.single a r), unitsMatrixPiHom_elementaryUnit i j hij a r⟩)
  rwa [Subgroup.pi_top] at hle

theorem unitsMatrixPiHom_surjective [Fintype α] [DecidableEq α]
    (hA : ∀ a, elementaryGroup ι (A a) = ⊤) :
    Function.Surjective (unitsMatrixPiHom (ι := ι) (A := A)) := fun w ↦ by
  obtain ⟨v, -, hv⟩ := top_le_map_unitsMatrixPiHom hA (Subgroup.mem_top w)
  exact ⟨v, hv⟩

/-- `GL_n(∏_a A_a) ≃* ∏_a GL_n(A_a)` when every factor has `GL_n = EL_n`. -/
noncomputable def unitsMatrixPiEquiv [Fintype α] [DecidableEq α]
    (hA : ∀ a, elementaryGroup ι (A a) = ⊤) :
    (Matrix ι ι (∀ a, A a))ˣ ≃* ∀ a, (Matrix ι ι (A a))ˣ :=
  MulEquiv.ofBijective (unitsMatrixPiHom (ι := ι) (A := A))
    ⟨unitsMatrixPiHom_injective, unitsMatrixPiHom_surjective hA⟩

/-- **`EL_n` of a finite product of rings is everything when every factor is.** -/
theorem elementaryGroup_pi_eq_top [Fintype α] [DecidableEq α]
    (hA : ∀ a, elementaryGroup ι (A a) = ⊤) :
    elementaryGroup ι (∀ a, A a) = ⊤ := by
  refine eq_top_iff.2 fun u _ ↦ ?_
  obtain ⟨v, hv, hvu⟩ :=
    top_le_map_unitsMatrixPiHom hA (Subgroup.mem_top (unitsMatrixPiHom (ι := ι) (A := A) u))
  rw [← unitsMatrixPiHom_injective hvu]
  exact hv

/-- **`GL_n(B) = EL_n(B)` for `n ≥ 2` and `B = ∏_a M_{h_a}(F_2)`.** -/
theorem elementaryGroup_matrixProductFTwo_eq_top [Nontrivial ι] (m : ℕ) (h : Fin m → ℕ) :
    elementaryGroup ι (MatrixProductFTwo m h) = ⊤ :=
  elementaryGroup_pi_eq_top (A := fun a ↦ Matrix (Fin (h a)) (Fin (h a)) (ZMod 2))
    fun a ↦ elementaryGroup_matrix_zmodTwo_eq_top (Fin (h a))

end Pi

section SL

/-- **Every invertible matrix over `F_2` has determinant one.** -/
theorem det_units_zmodTwo {N : Type*} [Fintype N] [DecidableEq N]
    (u : (Matrix N N (ZMod 2))ˣ) : (u : Matrix N N (ZMod 2)).det = 1 := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact key _ (Matrix.isUnits_det_units u).ne_zero

/-- `GL_N(F_2) ≃* SL_N(F_2)`. -/
noncomputable def unitsZModTwoEquivSL (N : Type*) [Fintype N] [DecidableEq N] :
    (Matrix N N (ZMod 2))ˣ ≃* SpecialLinearGroup N (ZMod 2) :=
  (MulEquiv.ofBijective (SpecialLinearGroup.toGL (n := N) (R := ZMod 2))
    ⟨SpecialLinearGroup.toGL_injective,
      fun u ↦ ⟨⟨(u : Matrix N N (ZMod 2)), det_units_zmodTwo u⟩, Units.ext rfl⟩⟩).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`EL_n(B) ≃* ∏_a SL_{n h_a}(F_2)` for `n ≥ 2` and `B = ∏_a M_{h_a}(F_2)`.** -/
noncomputable def elementaryMatrixProductFTwoEquiv [Nontrivial ι] (m : ℕ) (h : Fin m → ℕ) :
    elementaryGroup ι (MatrixProductFTwo m h) ≃*
      ∀ a : Fin m, SpecialLinearGroup (ι × Fin (h a)) (ZMod 2) :=
  ((MulEquiv.subgroupCongr (elementaryGroup_matrixProductFTwo_eq_top m h)).trans
    Subgroup.topEquiv).trans <|
      (unitsMatrixPiEquiv (A := fun a ↦ Matrix (Fin (h a)) (Fin (h a)) (ZMod 2))
        fun a ↦ elementaryGroup_matrix_zmodTwo_eq_top (Fin (h a))).trans <|
        MulEquiv.piCongrRight fun a ↦
          (elementaryBlockUnitEquiv (ι := ι) (κ := Fin (h a)) (R := ZMod 2)).trans
            (unitsZModTwoEquivSL (ι × Fin (h a)))

end SL

end ChainRadical
end GroupApproximation

#audit_axioms GroupApproximation.ChainRadical.elementaryGroup_matrix_zmodTwo_eq_top
#audit_axioms GroupApproximation.ChainRadical.unitsMatrixPiHom_injective
#audit_axioms GroupApproximation.ChainRadical.unitsMatrixPiHom_elementaryUnit
#audit_axioms GroupApproximation.ChainRadical.unitsMatrixPiEquiv
#audit_axioms GroupApproximation.ChainRadical.elementaryGroup_pi_eq_top
#audit_axioms GroupApproximation.ChainRadical.elementaryGroup_matrixProductFTwo_eq_top
#audit_axioms GroupApproximation.ChainRadical.det_units_zmodTwo
#audit_axioms GroupApproximation.ChainRadical.unitsZModTwoEquivSL
#audit_axioms GroupApproximation.ChainRadical.elementaryMatrixProductFTwoEquiv
