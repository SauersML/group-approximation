import GroupApproximation.Manuscript.NonMF.Full.AtomRepresentatives.AtomCells
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices`, proof: the atom sentences as printed

`non_mf_groups_exist.tex`, proof of `\label{lem:transient-matrices}`, tex 1510–1517:

> Choose a finite clopen partition of $C$ separating distinct points
> in each class: the finitely many nonidentity partial shifts have no
> fixed points, so compactness gives such a partition.  Order its atoms
> and select the point in the first occupied atom as the class
> representative.  The representative set is clopen, because presence
> of a related point in an earlier atom is a finite clopen test.
> Refine it according to the occupied atoms, the shift exponents to
> each level, and all original coefficient values.

The class of `x ∈ C` is `ChainCore.reachableExponents T C E (m - 1) x` (as exponents), `m` the orbit
bound on `C`.  The separating atoms, the first-atom representative set `atomBaseSet` and the refined
cells are those of `Full.NM19` (`SeparatingAtoms`, `AtomBaseSet`, `AtomCells`).  This module states
the four sentences one by one:

* `manuscriptSentence_separatingAtomPartition` (tex 1510–1512): nonzero powers of `T` fix no point of
  `C`, and a finite clopen partition of `C` separating the points of each class exists;
* `mem_atomBaseSet_iff`, `manuscriptSentence_firstOccupiedAtomRepresentative` (tex 1512–1514): the
  representative is the point of its class lying in the first occupied atom, and every class has
  exactly one;
* `earlierAtomTest`, `manuscriptSentence_representativeSetClopen` (tex 1514–1515): the points of `C`
  with a related point in an earlier atom form a clopen set, and the representative set is its
  complement in `C`, hence clopen;
* `manuscriptSentence_refineByAtomsExponentsCoefficients` (tex 1515–1517): the refinement of the
  representative set by the occupied atoms, the class exponents and finitely many locally constant
  values (the coefficients); `NM19.exists_transientCells_atoms` is the same refinement for the
  coefficients of a finite subset of the transient ideal.
-/

namespace GroupApproximation.Full.NMRegradeA

open GroupApproximation.ChainCore
open GroupApproximation.Full.NM19

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m N : ℕ}

/-- **"Choose a finite clopen partition of $C$ separating distinct points in each class: the finitely
many nonidentity partial shifts have no fixed points, so compactness gives such a partition"**
(tex 1510–1512). -/
theorem manuscriptSentence_separatingAtomPartition [CompactSpace X] [TotallySeparatedSpace X]
    (hC : IsClopen C) (hm : ExponentBound T C m) (E : Finset ℤ) :
    (∀ y ∈ C, ∀ e : ℤ, e ≠ 0 → (T ^ e) y ≠ y) ∧
      ∃ (N : ℕ) (atom : Fin N → Set X), IsSeparatingAtoms T C E m N atom :=
  ⟨fun _ hy _ he => zpow_apply_ne_of_exponentBound hm hy he, exists_separating_atoms hC hm E⟩

/-- **The representative lies in the first occupied atom** (tex 1512–1514): `x` is a representative
exactly when `x ∈ C` and no point of its class lies in an atom of smaller index than the atom of `x`. -/
theorem mem_atomBaseSet_iff {atom : Fin N → Set X} {x : X} :
    x ∈ atomBaseSet T C E m N atom ↔ x ∈ C ∧ ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
      x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j :=
  Iff.rfl

/-- **"Order its atoms and select the point in the first occupied atom as the class
representative"** (tex 1512–1514): every point `z ∈ C` reaches a representative inside its class,
and exactly one exponent of the class of `z` does. -/
theorem manuscriptSentence_firstOccupiedAtomRepresentative (hm : ExponentBound T C m)
    {atom : Fin N → Set X} (hatoms : IsSeparatingAtoms T C E m N atom) {z : X} (hz : z ∈ C) :
    ∃ e ∈ reachableExponents T C E (m - 1) z, (T ^ e) z ∈ atomBaseSet T C E m N atom ∧
      ∀ e' ∈ reachableExponents T C E (m - 1) z,
        (T ^ e') z ∈ atomBaseSet T C E m N atom → e' = e := by
  obtain ⟨e, he, hrep⟩ := exists_zpow_mem_atomBaseSet hm hatoms hz
  refine ⟨e, he, hrep, fun e' he' hrep' => ?_⟩
  have hback : ∀ a : ℤ, (T ^ (-a)) ((T ^ a) z) = z := fun a => by
    rw [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  have h := eq_of_zpow_eq_of_mem_atomBaseSet hm hatoms hrep' hrep
    (neg_mem_reachableExponents (m - 1) he') (neg_mem_reachableExponents (m - 1) he)
    (by rw [hback e', hback e])
  have h2 : -e' = -e := h.2
  omega

/-- The finite clopen test of tex 1514–1515: the points of `C` with a related point in an earlier
atom than their own. -/
def earlierAtomTest (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m N : ℕ) (atom : Fin N → Set X) :
    Set X :=
  {x | ∃ d ∈ reachableExponents T C E (m - 1) x, ∃ i j, x ∈ atom i ∧ (T ^ d) x ∈ atom j ∧ j < i}

/-- **"The representative set is clopen, because presence of a related point in an earlier atom is
a finite clopen test"** (tex 1514–1515). -/
theorem manuscriptSentence_representativeSetClopen (hC : IsClopen C) {atom : Fin N → Set X}
    (hatom : ∀ i, IsClopen (atom i)) :
    IsClopen (earlierAtomTest T C E m N atom) ∧
      atomBaseSet T C E m N atom = C \ earlierAtomTest T C E m N atom ∧
      IsClopen (atomBaseSet T C E m N atom) := by
  have hA : IsClopen {x | ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
      x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j} := by
    have h := (isLocallyConstant_atomTest (T := T) (E := E) (m := m) hC hatom).isClopen_fiber True
    have hset : {x | ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
        x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j} =
        {x | (fun x => ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
          x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j) x = True} :=
      Set.ext fun _ => ⟨eq_true, of_eq_true⟩
    rw [hset]
    exact h
  have hB : earlierAtomTest T C E m N atom = {x | ∀ d ∈ reachableExponents T C E (m - 1) x,
      ∀ i j, x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j}ᶜ := by
    ext x
    simp only [earlierAtomTest, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨d, hd, i, j, hi, hj, hji⟩ hall
      exact absurd (hall d hd i j hi hj) (not_le.2 hji)
    · intro hx
      by_contra hne
      refine hx fun d hd i j hi hj => ?_
      by_contra hij
      exact hne ⟨d, hd, i, j, hi, hj, not_le.1 hij⟩
  have hbase : atomBaseSet T C E m N atom = C \ earlierAtomTest T C E m N atom := by
    unfold atomBaseSet
    rw [hB, Set.sdiff_eq, compl_compl]
  refine ⟨?_, hbase, isClopen_atomBaseSet hC hatom⟩
  rw [hB]
  exact hA.compl

/-- **"Refine it according to the occupied atoms, the shift exponents to each level, and all
original coefficient values"** (tex 1515–1517), for finitely many locally constant values `g`
(the coefficients): finitely many pairwise disjoint nonempty clopen cells inside the representative
set, covering it, on which the class exponents, the occupied atoms at the exponents `D` and the
values `g` are constant. -/
theorem manuscriptSentence_refineByAtomsExponentsCoefficients [CompactSpace X] (hC : IsClopen C)
    {atom : Fin N → Set X} (hatom : ∀ i, IsClopen (atom i)) (D : Finset ℤ) {ι Z : Type*}
    [Finite ι] (g : ι → X → Z) (hg : ∀ i, IsLocallyConstant (g i)) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
      (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ atomBaseSet T C E m N atom) ∧
      (∀ a, ∀ y ∈ cell a, reachableExponents T C E (m - 1) y = S a) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ atomBaseSet T C E m N atom, ∃ a, y ∈ cell a) ∧
      (∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ D, ∀ i,
        ((T ^ d) y ∈ atom i ↔ (T ^ d) y' ∈ atom i)) ∧
      ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ i, g i y = g i y' :=
  exists_atomCells (T := T) (E := E) (m := m) hC hatom D g hg

end GroupApproximation.Full.NMRegradeA

#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_separatingAtomPartition
#audit_axioms GroupApproximation.Full.NMRegradeA.mem_atomBaseSet_iff
#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_firstOccupiedAtomRepresentative
#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_representativeSetClopen
#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_refineByAtomsExponentsCoefficients
