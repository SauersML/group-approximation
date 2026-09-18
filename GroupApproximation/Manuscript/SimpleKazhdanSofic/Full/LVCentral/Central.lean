import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Vectors

/-!
# Stabilized `K₂` is central one rank up (Khanh, Lemma 5.2)

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. The Leavitt route to that claim goes through
`K₂(4, L) = ⊥` for the binary Leavitt algebra `L`. Khanh's proof (arXiv:2609.08428, Theorem 5.1)
relies on Lemma 5.2 (Lemma 5.6 in the foreign `LeavittK2` code): for every ring `B` and every
`m`, the stabilization `St_m(B) → St_{m+1}(B)` sends `K₂(m, B)` into the centre of
`St_{m+1}(B)`. This file proves that lemma unconditionally. It is leaf T1b.ii of the
`K₂(4, L) = ⊥` tree.

The padded form needs no rank hypothesis. Centrality of `K₂(m, B)` inside `St_m(B)` itself is
not known for arbitrary noncommutative rings, and it is not claimed here.

A stabilized `K₂` element commutes with the column roots `x_{i,m}(a)` and the row roots
`x_{m,j}(a)` (`LVCentral.Vectors`). Every other generator is a commutator
`x_{i,j}(a) = ⁅x_{i,m}(a), x_{m,j}(1)⁆`, so the element commutes with all generators.
-/

namespace GroupApproximation
namespace Full
namespace LVCentral

open SteinbergGroup

variable {B : Type*} [Ring B] {m : ℕ}

/-- A stabilized `K₂` element commutes with every Steinberg generator of `St_{m+1}(B)`. -/
theorem commute_x_of_projection_eq_one {g : SteinbergGroup (Fin m) B} (hg : projection g = 1)
    (p q : Fin (m + 1)) (hpq : p ≠ q) (a : B) :
    Commute (castSuccStab m B g) (x p q hpq a) := by
  induction p using Fin.lastCases with
  | last =>
      induction q using Fin.lastCases with
      | last => exact (hpq rfl).elim
      | cast j => exact commute_rowRoot_of_projection_eq_one hg j a
  | cast i =>
      induction q using Fin.lastCases with
      | last => exact commute_colRoot_of_projection_eq_one hg i a
      | cast j =>
          have hc := commute_colRoot_of_projection_eq_one hg i a
          have hr := commute_rowRoot_of_projection_eq_one hg j 1
          have hcomm := x_commutator i.castSucc (Fin.last m) j.castSucc
            (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j).symm hpq a 1
          rw [mul_one] at hcomm
          rw [← hcomm, commutatorElement_def]
          exact ((hc.mul_right hr).mul_right hc.inv_right).mul_right hr.inv_right

/-- **Khanh, Lemma 5.2** (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.ii): a stabilized
`K₂` element is central one rank up. Holds for every ring `B` and every `m`. -/
theorem castSuccStab_mem_center {g : SteinbergGroup (Fin m) B}
    (hg : g ∈ (projection (I := Fin m) (R := B)).ker) :
    castSuccStab m B g ∈ Subgroup.center (SteinbergGroup (Fin (m + 1)) B) := by
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_center_iff]
  intro h
  have hh : h ∈ Subgroup.centralizer {castSuccStab m B g} := by
    refine PresentedGroup.generated_by _ _ ?_ h
    rintro ⟨p, q, hpq, a⟩
    change x p q hpq a ∈ Subgroup.centralizer {castSuccStab m B g}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_x_of_projection_eq_one hg p q hpq a).symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hh
  exact hh

/-- **Khanh, Lemma 5.2, subgroup form** (`simple_kazhdan_sofic_group.tex` l.733-735): the image of
`K₂(m, B)` under stabilization lies in the centre of `St_{m+1}(B)`. -/
theorem map_ker_projection_le_center :
    (projection (I := Fin m) (R := B)).ker.map (castSuccStab m B) ≤
      Subgroup.center (SteinbergGroup (Fin (m + 1)) B) := by
  rintro _ ⟨g, hg, rfl⟩
  exact castSuccStab_mem_center hg

/-- Stabilizing twice also lands in the centre, since stabilization preserves `K₂`. -/
theorem castSuccStab_castSuccStab_mem_center {g : SteinbergGroup (Fin m) B}
    (hg : g ∈ (projection (I := Fin m) (R := B)).ker) :
    castSuccStab (m + 1) B (castSuccStab m B g) ∈
      Subgroup.center (SteinbergGroup (Fin (m + 1 + 1)) B) :=
  castSuccStab_mem_center (castSuccStab_mem_ker hg)

end LVCentral
end Full
end GroupApproximation
