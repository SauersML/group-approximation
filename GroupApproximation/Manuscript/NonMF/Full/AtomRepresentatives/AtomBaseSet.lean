import GroupApproximation.Manuscript.NonMF.Full.AtomRepresentatives.SeparatingAtoms
import GroupApproximation.Meta.AxiomGuard

/-!
# The representative in the first occupied atom

`non_mf_groups_exist.tex`, `\label{lem:transient-matrices}`, proof, tex 1512–1515:

> Order its atoms
> and select the point in the first occupied atom as the class
> representative.  The representative set is clopen, because presence
> of a related point in an earlier atom is a finite clopen test.

For separating atoms `atom : Fin N → Set X` of `C` (`IsSeparatingAtoms`, tex 1510–1512), ordered by
their index:

* `atomBaseSet T C E m N atom`: the points `x ∈ C` such that no point of the class of `x` lies in an
  earlier atom than `x`;
* `isLocallyConstant_atomTest`, `isClopen_atomBaseSet`: the representative set is clopen, since
  the test only looks at finitely many exponents and atoms;
* `exists_zpow_mem_atomBaseSet`: every point of `C` reaches a representative inside its class;
* `eq_of_zpow_eq_of_mem_atomBaseSet`: a class has exactly one representative, and the exponent
  from the representative to a point of the class is unique.
-/

namespace GroupApproximation.Full.NM19

open GroupApproximation.ChainCore
open Topology

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m N : ℕ}

/-- **The representative set** (tex 1512–1514): points of `C` in the first atom occupied by their
class. -/
def atomBaseSet (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m N : ℕ) (atom : Fin N → Set X) :
    Set X :=
  C ∩ {x | ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
    x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j}

/-- **A finite clopen test** (tex 1514–1515): whether a related point lies in an earlier atom is a
locally constant condition. -/
theorem isLocallyConstant_atomTest (hC : IsClopen C) {atom : Fin N → Set X}
    (hatom : ∀ i, IsClopen (atom i)) :
    IsLocallyConstant fun x => ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
      x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hR : ∀ᶠ y in 𝓝 x, reachableExponents T C E (m - 1) y =
      reachableExponents T C E (m - 1) x :=
    (isLocallyConstant_reachableExponents hC (m - 1)).eventually_eq x
  have hA : ∀ᶠ y in 𝓝 x, ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i,
      ((T ^ d) y ∈ atom i ↔ (T ^ d) x ∈ atom i) :=
    (Filter.eventually_all_finset _).2 fun d _ =>
      Filter.eventually_all.2 fun i => eventually_zpow_mem_iff (T := T) (hatom i) d x
  have h0 : ∀ᶠ y in 𝓝 x, ∀ i, ((T ^ (0 : ℤ)) y ∈ atom i ↔ (T ^ (0 : ℤ)) x ∈ atom i) :=
    Filter.eventually_all.2 fun i => eventually_zpow_mem_iff (T := T) (hatom i) 0 x
  filter_upwards [hR, hA, h0] with y hRy hAy h0y
  simp only [zpow_zero, Homeomorph.one_apply] at h0y
  refine propext ⟨fun h d hd i j hi hj => ?_, fun h d hd i j hi hj => ?_⟩
  · have hd' : d ∈ reachableExponents T C E (m - 1) y := by
      rw [hRy]
      exact hd
    exact h d hd' i j ((h0y i).2 hi) ((hAy d hd j).2 hj)
  · have hd' : d ∈ reachableExponents T C E (m - 1) x := by
      rw [← hRy]
      exact hd
    exact h d hd' i j ((h0y i).1 hi) ((hAy d hd' j).1 hj)

/-- **The representative set is clopen** (tex 1514–1515). -/
theorem isClopen_atomBaseSet (hC : IsClopen C) {atom : Fin N → Set X}
    (hatom : ∀ i, IsClopen (atom i)) : IsClopen (atomBaseSet T C E m N atom) := by
  have h := (isLocallyConstant_atomTest (T := T) (E := E) (m := m) hC hatom).isClopen_fiber True
  have hset : {x | ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
      x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j} =
      {x | (fun x => ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
        x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j) x = True} :=
    Set.ext fun _ => ⟨eq_true, of_eq_true⟩
  show IsClopen (C ∩ {x | ∀ d ∈ reachableExponents T C E (m - 1) x, ∀ i j,
    x ∈ atom i → (T ^ d) x ∈ atom j → i ≤ j})
  rw [hset]
  exact hC.inter h

theorem exists_mem_atom {atom : Fin N → Set X} (hatoms : IsSeparatingAtoms T C E m N atom)
    {z : X} (hz : z ∈ C) : ∃ i, z ∈ atom i := by
  have hz' : z ∈ ⋃ i, atom i := by
    rw [← hatoms.iUnion_eq]
    exact hz
  exact Set.mem_iUnion.1 hz'

/-- **Every class has a representative** (tex 1512–1514): the point of the class in the first
occupied atom. -/
theorem exists_zpow_mem_atomBaseSet (hm : ExponentBound T C m) {atom : Fin N → Set X}
    (hatoms : IsSeparatingAtoms T C E m N atom) {z : X} (hz : z ∈ C) :
    ∃ e ∈ reachableExponents T C E (m - 1) z, (T ^ e) z ∈ atomBaseSet T C E m N atom := by
  classical
  obtain ⟨Occ, hOcc⟩ : ∃ Occ : Finset (Fin N), Occ = Finset.univ.filter fun j =>
      ∃ d ∈ reachableExponents T C E (m - 1) z, (T ^ d) z ∈ atom j := ⟨_, rfl⟩
  have hmemOcc : ∀ j, j ∈ Occ ↔ ∃ d ∈ reachableExponents T C E (m - 1) z, (T ^ d) z ∈ atom j :=
    fun j => by
      rw [hOcc, Finset.mem_filter]
      exact and_iff_right (Finset.mem_univ j)
  obtain ⟨i0, hi0⟩ := exists_mem_atom hatoms hz
  have hne : Occ.Nonempty := ⟨i0, (hmemOcc i0).2 ⟨0, zero_mem_reachableExponents hz, by
    rw [zpow_zero, Homeomorph.one_apply]
    exact hi0⟩⟩
  obtain ⟨d0, hd0, hd0i⟩ := (hmemOcc _).1 (Finset.min'_mem Occ hne)
  refine ⟨d0, hd0, zpow_mem_of_mem_reachableExponents hd0, fun d hd i j hi hj => ?_⟩
  have hii : i = Occ.min' hne := by
    by_contra hne'
    exact Set.disjoint_left.1 (hatoms.disjoint i _ hne') hi hd0i
  rw [reachableExponents_zpow_eq hm hd0, Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  rw [Dynamics.zpow_apply_zpow_apply, sub_add_cancel] at hj
  rw [hii]
  exact Finset.min'_le Occ j ((hmemOcc j).2 ⟨c, hc, hj⟩)

/-- **Representatives are unique** (tex 1512–1514): a point reached from two representatives by
exponents of their classes determines the representative and the exponent. -/
theorem eq_of_zpow_eq_of_mem_atomBaseSet (hm : ExponentBound T C m) {atom : Fin N → Set X}
    (hatoms : IsSeparatingAtoms T C E m N atom) {x x' : X} {d d' : ℤ}
    (hx : x ∈ atomBaseSet T C E m N atom) (hx' : x' ∈ atomBaseSet T C E m N atom)
    (hd : d ∈ reachableExponents T C E (m - 1) x)
    (hd' : d' ∈ reachableExponents T C E (m - 1) x')
    (h : (T ^ d) x = (T ^ d') x') : x = x' ∧ d = d' := by
  have hz := reachableExponents_zpow_eq hm hd
  have hneg : -d' ∈ reachableExponents T C E (m - 1) ((T ^ d) x) := by
    rw [h]
    exact neg_mem_reachableExponents (m - 1) hd'
  rw [hz, Finset.mem_image] at hneg
  obtain ⟨c, hc, hcd⟩ := hneg
  have hx'eq : (T ^ c) x = x' := by
    have hc' : c = d - d' := by omega
    rw [hc']
    exact Dynamics.zpow_sub_apply_of_eq T h.symm
  have hnegc : -c ∈ reachableExponents T C E (m - 1) x' := by
    have h1 := neg_mem_reachableExponents (m - 1) hc
    rw [hx'eq] at h1
    exact h1
  have hback : (T ^ (-c)) x' = x := by
    rw [← hx'eq, Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  obtain ⟨i, hxi⟩ := exists_mem_atom hatoms hx.1
  obtain ⟨j, hx'j⟩ := exists_mem_atom hatoms hx'.1
  have hij : i ≤ j := hx.2 c hc i j hxi (by rw [hx'eq]; exact hx'j)
  have hji : j ≤ i := hx'.2 (-c) hnegc j i hx'j (by rw [hback]; exact hxi)
  have hieq : i = j := le_antisymm hij hji
  rw [← hieq] at hx'j
  have hc0 : (0 : ℤ) = c := hatoms.separates x 0 (zero_mem_reachableExponents hx.1) c hc i
    (by rw [zpow_zero, Homeomorph.one_apply]; exact hxi) (by rw [hx'eq]; exact hx'j)
  refine ⟨?_, by omega⟩
  rw [← hx'eq, ← hc0, zpow_zero, Homeomorph.one_apply]

end GroupApproximation.Full.NM19

#audit_axioms GroupApproximation.Full.NM19.isLocallyConstant_atomTest
#audit_axioms GroupApproximation.Full.NM19.isClopen_atomBaseSet
#audit_axioms GroupApproximation.Full.NM19.exists_mem_atom
#audit_axioms GroupApproximation.Full.NM19.exists_zpow_mem_atomBaseSet
#audit_axioms GroupApproximation.Full.NM19.eq_of_zpow_eq_of_mem_atomBaseSet
