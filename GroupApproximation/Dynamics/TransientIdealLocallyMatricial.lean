import GroupApproximation.Dynamics.TransientTowerExpansion
import GroupApproximation.Dynamics.ClopenCrossedProductAlgebra
import GroupApproximation.Dynamics.CoreKernelFTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices`: the transient ideal is locally matricial

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}` (tex 1476):

> The ideal $I$ is locally matricial [...]

and the last sentence of its proof (tex 1512–1513):

> The characteristic arrows between these levels form a copy of $M_h(k)$.  The product of these
> finitely many matrix algebras contains the prescribed elements, proving local matriciality.

The assembly follows the printed route through chain-matricial's criterion
`ChainCore.isLocallyMatricialIn_of_forall_exists_family`.  For a finite subset `F` of `I` it uses
* the matrix unit family of the tower levels (`isMatrixUnitFamily_transientTower`), with nonzero
  diagonal (`transientTowerUnit_self_ne_zero`) and units in `I`
  (`transientTowerUnit_mem_transientIdeal`);
* the expansion of each prescribed element in these units (`exists_matrix_eq_sum_transientTower`).

The cells themselves come from `TransientCellsStatement` (tex 1489–1511):
* a clopen `C ⊆ X ∖ Y` containing the sources and ranges;
* the step exponents `E` and the orbit bound `m`;
* finitely many pairwise disjoint nonempty clopen cells inside the representative sets, covering
  every representative, on which all coefficient values of `F` are constant at every level.
Owner ct-involution.

* `transientIdealLocallyMatricial_of_cells`: ms-compress-3's
  `ChainCore.TransientIdealLocallyMatricialStatement`, over every finite field.
* `transientIdealLocallyMatricialFTwo_of_cells`: the input of `CoreKernelFTwo` over `F₂`.
* `coreKernelElementaryStatement_of_cells`, `unitKernelLocallyFinite_of_cells`: the two kernel
  clauses of `lem:involution-localization` over the same input.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open ChainCore
open Multiplicative (toAdd)

/-- **The cells of `lem:transient-matrices`** (tex 1489–1511), for a finite subset `F` of the
transient ideal: a clopen `C` avoiding `Y = CR(T)`, step exponents `E` with the orbit bound `m` on
`C`, and finitely many pairwise disjoint clopen cells inside the representative sets, each with a
chosen point, covering every representative, such that every coefficient of `F` vanishes off the
sources and ranges in `C` and is constant on each level of each cell.  Owner ct-involution. -/
def TransientCellsStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Ring k] (F : Finset (ClopenCrossedProduct T k)),
    (∀ x ∈ F, x ∈ transientIdeal T k (Dynamics.image_chainRecurrentSet T)) →
    ∃ (C : Set X) (E : Finset ℤ) (m M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ)
      (_ : ∀ a, IsClopen (cell a)) (rep : Fin M → X),
      IsClopen C ∧ Disjoint C (Dynamics.chainRecurrentSet ⇑T) ∧ ExponentBound T C m ∧
      (∀ a, cell a ⊆ baseCell T C E m (S a)) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧
      (∀ y ∈ baseSet T C E m, ∃ a, y ∈ cell a) ∧
      (∀ a, rep a ∈ cell a) ∧
      (∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, toAdd g ∈ E ∧
        ∀ z, (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0 →
          z ∈ C ∧ (T ^ (-toAdd g)) z ∈ C) ∧
      ∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a,
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y) =
          (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y')

/-- **`lem:transient-matrices`, the locally matricial clause** (tex 1476), over the cells: the
transient ideal of `R_X` over every finite field is locally matricial. -/
theorem transientIdealLocallyMatricial_of_cells (h : TransientCellsStatement) :
    TransientIdealLocallyMatricialStatement := by
  intro X _ _ _ T k _ _
  refine isLocallyMatricialIn_of_forall_exists_family
    (zero_mem (transientIdeal T k (Dynamics.image_chainRecurrentSet T)))
    (fun x hx y hy => add_mem (s := transientIdeal T k (Dynamics.image_chainRecurrentSet T)) hx hy)
    (fun c x hx => smul_mem_transientIdeal T k (Dynamics.image_chainRecurrentSet T) c hx) ?_
  intro F hF
  obtain ⟨C, E, m, M, cell, S, hcell, rep, -, hCY, hm, hsub, hdisj, hcover, hrep, hx, hconst⟩ :=
    h X T k F hF
  exact ⟨M, fun a => (S a).card,
    Pestov91.CrossedProduct.towerUnit (transientTowerCoeff T k cell S hcell) (transientTowerExp S),
    isMatrixUnitFamily_transientTower k hcell hm hsub hdisj,
    fun a i => transientTowerUnit_self_ne_zero k hcell (fun a => ⟨rep a, hrep a⟩) a i,
    fun a i j => transientTowerUnit_mem_transientIdeal k hcell (Dynamics.image_chainRecurrentSet T)
      hCY hsub a i j,
    fun x hxF => exists_matrix_eq_sum_transientTower k hcell hm hsub hdisj hcover rep hrep x
      (hx x hxF) (hconst x hxF)⟩

/-- **The transient ideal over `F₂` is locally matricial** in the form `CoreKernelFTwo` consumes. -/
theorem transientIdealLocallyMatricialFTwo_of_cells (h : TransientCellsStatement) :
    TransientIdealLocallyMatricialFTwoStatement := by
  intro X _ _ _ _ T F hF
  exact (transientIdealLocallyMatricial_of_cells h X T (ZMod 2)).exists_nonUnitalRingHom F hF

/-- **`K_n(I) ⊆ EL_n(R_X)` over `F₂` for `n ≥ 2`**, over the cells. -/
theorem coreKernelElementaryStatement_of_cells (h : TransientCellsStatement) :
    CoreKernelElementaryStatement :=
  coreKernelElementaryStatement_of_matricial (transientIdealLocallyMatricialFTwo_of_cells h)

/-- **`K_1(I)` is locally finite over `F₂`**, over the cells. -/
theorem unitKernelLocallyFinite_of_cells (h : TransientCellsStatement) :
    DynamicRankBudget.UnitKernelLocallyFiniteStatement :=
  unitKernelLocallyFinite_of_matricial (transientIdealLocallyMatricialFTwo_of_cells h)

end ClopenCrossedProduct
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.ClopenCrossedProduct.transientIdealLocallyMatricial_of_cells
#audit_axioms GroupApproximation.ClopenCrossedProduct.transientIdealLocallyMatricialFTwo_of_cells
#audit_axioms GroupApproximation.ClopenCrossedProduct.coreKernelElementaryStatement_of_cells
#audit_axioms GroupApproximation.ClopenCrossedProduct.unitKernelLocallyFinite_of_cells
