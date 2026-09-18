import GroupApproximation.Manuscript.NonMF.Full.AtomRepresentatives.AtomBaseSet
import GroupApproximation.Dynamics.TransientCellsClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The cells of `lem:transient-matrices` over first-atom representatives

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1510–1517:

> Choose a finite clopen partition of $C$ separating distinct points
> in each class [...].  Order its atoms
> and select the point in the first occupied atom as the class
> representative.  The representative set is clopen [...].
> Refine it according to the occupied atoms, the shift exponents to each level,
> and all original coefficient values.

Over the separating atoms (`exists_separating_atoms`) and the first-atom representative set
`atomBaseSet` (`AtomBaseSet`) this module refines the representative set as printed:

* `isLocallyConstant_zpow_mem`: occupancy of a clopen atom at a fixed exponent is locally constant;
* `exists_cells_of_isClopen`: a clopen set refined by a locally constant function splits into
  finitely many pairwise disjoint nonempty clopen cells on which the function is constant;
* `exists_atomCells`: the first-atom representative set refined by the class exponents, the
  occupied atoms at every level and finitely many locally constant values;
* `exists_transientCells_atoms`: the conclusion of `ClopenCrossedProduct.exists_transientCells`
  with separating atoms, cells inside the first-atom representative set covering it, constant class
  exponents and occupied atoms on each cell, and constant coefficient values at every level.

The section `C`, the exponents `E`, the orbit bound and the support clause are those of the closed
`ClopenCrossedProduct.transientCellsStatement_holds`; only the cells are rebuilt.
-/

namespace GroupApproximation.Full.NM19

open GroupApproximation.ChainCore
open Multiplicative (toAdd)
open Topology

section Cells

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m N : ℕ}

/-- **Occupancy is a clopen test** (tex 1514–1516): whether `T^d y` lies in a clopen atom is locally
constant in `y`. -/
theorem isLocallyConstant_zpow_mem {A : Set X} (hA : IsClopen A) (d : ℤ) :
    IsLocallyConstant fun y => (T ^ d) y ∈ A :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (eventually_zpow_mem_iff (T := T) hA d x).mono fun _ hy => propext hy

/-- **Refining a clopen set** (tex 1516–1517): the fibres of a locally constant function on a clopen
subset of a compact space are finitely many pairwise disjoint nonempty clopen cells. -/
theorem exists_cells_of_isClopen [CompactSpace X] {B : Set X} (hB : IsClopen B) {Z : Type*}
    {φ : X → Z} (hφ : IsLocallyConstant φ) :
    ∃ (M : ℕ) (cell : Fin M → Set X), (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ B) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ B, ∃ a, y ∈ cell a) ∧ ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, φ y = φ y' := by
  classical
  have hfin := hφ.range_finite
  obtain ⟨V, hVdef⟩ : ∃ V : Finset Z,
      V = hfin.toFinset.filter fun v => (B ∩ {y | φ y = v}).Nonempty := ⟨_, rfl⟩
  refine ⟨V.card, fun a => B ∩ {y | φ y = (V.equivFin.symm a).1},
    fun _ => hB.inter (hφ.isClopen_fiber _), fun _ => Set.inter_subset_left,
    fun a b hab => ?_, fun a => ?_, fun y hy => ?_, fun a y hy y' hy' => ?_⟩
  · rw [Set.disjoint_left]
    rintro y ⟨-, hya⟩ ⟨-, hyb⟩
    have hya' : φ y = (V.equivFin.symm a).1 := hya
    have hyb' : φ y = (V.equivFin.symm b).1 := hyb
    exact hab (V.equivFin.symm.injective (Subtype.ext (hya'.symm.trans hyb')))
  · have hVne : ∀ v ∈ V, (B ∩ {y | φ y = v}).Nonempty := fun v hv => by
      rw [hVdef, Finset.mem_filter] at hv
      exact hv.2
    exact hVne _ (V.equivFin.symm a).2
  · have hv : φ y ∈ V := by
      rw [hVdef, Finset.mem_filter]
      exact ⟨hfin.mem_toFinset.2 ⟨y, rfl⟩, ⟨y, hy, rfl⟩⟩
    refine ⟨V.equivFin ⟨φ y, hv⟩, hy, ?_⟩
    show φ y = (V.equivFin.symm (V.equivFin ⟨φ y, hv⟩)).1
    rw [Equiv.symm_apply_apply]
  · have h1 : φ y = (V.equivFin.symm a).1 := hy.2
    have h2 : φ y' = (V.equivFin.symm a).1 := hy'.2
    exact h1.trans h2.symm

/-- **The atom-refined cells** (tex 1512–1517): the first-atom representative set refined by the
class exponents, the occupied atoms at the exponents `D`, and finitely many locally constant
values. -/
theorem exists_atomCells [CompactSpace X] (hC : IsClopen C) {atom : Fin N → Set X}
    (hatom : ∀ i, IsClopen (atom i)) (D : Finset ℤ) {ι Z : Type*} [Finite ι] (g : ι → X → Z)
    (hg : ∀ i, IsLocallyConstant (g i)) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
      (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ atomBaseSet T C E m N atom) ∧
      (∀ a, ∀ y ∈ cell a, reachableExponents T C E (m - 1) y = S a) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ atomBaseSet T C E m N atom, ∃ a, y ∈ cell a) ∧
      (∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ D, ∀ i,
        ((T ^ d) y ∈ atom i ↔ (T ^ d) y' ∈ atom i)) ∧
      ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ i, g i y = g i y' := by
  classical
  obtain ⟨φ, hφdef⟩ : ∃ φ : X → Finset ℤ × ({d // d ∈ D} × Fin N → Prop) × (ι → Z),
      φ = fun y => (reachableExponents T C E (m - 1) y,
        fun p : {d // d ∈ D} × Fin N => (T ^ p.1.1) y ∈ atom p.2, fun i => g i y) := ⟨_, rfl⟩
  have hφ : IsLocallyConstant φ := by
    rw [hφdef]
    exact (isLocallyConstant_reachableExponents hC (m - 1)).prodMk
      ((ClopenCrossedProduct.isLocallyConstant_pi fun p : {d // d ∈ D} × Fin N =>
        isLocallyConstant_zpow_mem (T := T) (hatom p.2) p.1.1).prodMk
        (ClopenCrossedProduct.isLocallyConstant_pi hg))
  obtain ⟨M, cell, hcell, hsub, hdisj, hne, hcov, hconst⟩ :=
    exists_cells_of_isClopen (isClopen_atomBaseSet (T := T) (E := E) (m := m) hC hatom) hφ
  have hφeq : ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a,
      (fun y => (reachableExponents T C E (m - 1) y,
        fun p : {d // d ∈ D} × Fin N => (T ^ p.1.1) y ∈ atom p.2, fun i => g i y)) y =
      (fun y => (reachableExponents T C E (m - 1) y,
        fun p : {d // d ∈ D} × Fin N => (T ^ p.1.1) y ∈ atom p.2, fun i => g i y)) y' :=
    fun a y hy y' hy' => by
      have h := hconst a y hy y' hy'
      rw [hφdef] at h
      exact h
  refine ⟨M, cell, fun a => reachableExponents T C E (m - 1) (hne a).some, hcell, hsub,
    fun a y hy => congrArg Prod.fst (hφeq a y hy _ (hne a).some_mem), hdisj, hne, hcov,
    fun a y hy y' hy' d hd i => Iff.of_eq
      (congrFun (congrArg Prod.fst (congrArg Prod.snd (hφeq a y hy y' hy'))) (⟨d, hd⟩, i)),
    fun a y hy y' hy' i =>
      congrFun (congrArg Prod.snd (congrArg Prod.snd (hφeq a y hy y' hy'))) i⟩

end Cells

/-- **The cells of `lem:transient-matrices` over first-atom representatives** (tex 1510–1517): a
clopen section `C` off `CR(T)` with the orbit bound, separating atoms of `C`, and finitely many
pairwise disjoint clopen cells inside the first-atom representative set, covering it, each with a
point, on which the class exponents, the occupied atoms at every level and every coefficient value
of `F` at every level are constant. -/
theorem exists_transientCells_atoms (X : Type) [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] (T : X ≃ₜ X) (k : Type) [Ring k]
    (F : Finset (ClopenCrossedProduct T k))
    (hF : ∀ x ∈ F, x ∈ ClopenCrossedProduct.transientIdeal T k (Dynamics.image_chainRecurrentSet T)) :
    ∃ (C : Set X) (E : Finset ℤ) (m N M : ℕ) (atom : Fin N → Set X) (cell : Fin M → Set X)
      (S : Fin M → Finset ℤ) (rep : Fin M → X),
      IsClopen C ∧ Disjoint C (Dynamics.chainRecurrentSet ⇑T) ∧ ExponentBound T C m ∧
      IsSeparatingAtoms T C E m N atom ∧
      (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ atomBaseSet T C E m N atom) ∧
      (∀ a, ∀ y ∈ cell a, reachableExponents T C E (m - 1) y = S a) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧
      (∀ y ∈ atomBaseSet T C E m N atom, ∃ a, y ∈ cell a) ∧
      (∀ a, rep a ∈ cell a) ∧
      (∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ i,
        ((T ^ d) y ∈ atom i ↔ (T ^ d) y' ∈ atom i)) ∧
      (∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, toAdd g ∈ E ∧
        ∀ z, (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) z ≠ 0 →
          z ∈ C ∧ (T ^ (-toAdd g)) z ∈ C) ∧
      ∀ x ∈ F, ∀ g ∈ SkewMonoidAlgebra.support x, ∀ a, ∀ d ∈ S a, ∀ y ∈ cell a, ∀ y' ∈ cell a,
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y) =
          (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) ((T ^ d) y') := by
  classical
  obtain ⟨C, E, m, _M₀, _cell₀, _S₀, _hcell₀, _rep₀, hC, hCY, hm, -, -, -, -, hsupp, -⟩ :=
    ClopenCrossedProduct.transientCellsStatement_holds X T k F hF
  obtain ⟨N, atom, hatoms⟩ := exists_separating_atoms hC hm E
  obtain ⟨G, hGdef⟩ : ∃ G : Finset (Multiplicative ℤ),
      G = F.biUnion fun x => SkewMonoidAlgebra.support x := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := ClopenCrossedProduct.exists_finset_classExponents (T := T) (E := E) (m := m) hC
  obtain ⟨M, cell, S, hcell, hsub, hS, hdisj, hne, hcov, hocc, hconst⟩ :=
    exists_atomCells (T := T) (E := E) (m := m) hC hatoms.isClopen D
      (ι := {x // x ∈ F} × {g // g ∈ G} × {d // d ∈ D})
      (fun p y => (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff p.1.1 p.2.1.1)
        ((T ^ p.2.2.1) y))
      fun p => ((ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff p.1.1 p.2.1.1)).isLocallyConstant
        |>.comp_continuous (T ^ p.2.2.1).continuous
  refine ⟨C, E, m, N, M, atom, cell, S, fun a => (hne a).some, hC, hCY, hm, hatoms, hcell, hsub,
    hS, hdisj, hcov, fun a => (hne a).some_mem, fun a y hy y' hy' d hd i => ?_, hsupp,
    fun x hx g hg a d hd y hy y' hy' => ?_⟩
  · exact hocc a y hy y' hy' d (hD y (by rw [hS a y hy]; exact hd)) i
  · have hdD : d ∈ D := hD y (by rw [hS a y hy]; exact hd)
    have hgG : g ∈ G := by
      rw [hGdef]
      exact Finset.mem_biUnion.2 ⟨x, hx, hg⟩
    exact hconst a y hy y' hy' (⟨x, hx⟩, ⟨g, hgG⟩, ⟨d, hdD⟩)

end GroupApproximation.Full.NM19

#audit_axioms GroupApproximation.Full.NM19.isLocallyConstant_zpow_mem
#audit_axioms GroupApproximation.Full.NM19.exists_cells_of_isClopen
#audit_axioms GroupApproximation.Full.NM19.exists_atomCells
#audit_axioms GroupApproximation.Full.NM19.exists_transientCells_atoms
