import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Central

/-!
# Stabilization kills a coinvariant-trivial `K₂`

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`). This is the step of Khanh's proof
of Theorem 5.1 (arXiv:2609.08428) right after Lemma 5.2, used in step 4 of the LVStability route
(T1b.iii) and, at `m = 3`, `R = L`, in
`LeavittK2.stabKernelThreeTrivial_of_paddedCentral_of_superperfect`.

If `K₂(m, B) ≤ ⁅St_m(B), K₂(m, B)⁆`, then applying stabilization gives
`stab K₂(m) ≤ ⁅stab St_m, stab K₂(m)⁆ ≤ ⁅St_{m+1}, stab K₂(m)⁆`. The last group is trivial because
`stab K₂(m)` is central (`LVCentral.map_ker_projection_le_center`). So `stab K₂(m) = ⊥`. This holds
for every ring `B` and every `m`.
-/

namespace GroupApproximation
namespace Full
namespace LVCentral

open SteinbergGroup

variable {B : Type*} [Ring B] {m : ℕ}

/-- **Stabilization kills `K₂` when `K₂` is its own coinvariant commutator**
(`simple_kazhdan_sofic_group.tex` l.733-735; Khanh, proof of Thm 5.1). -/
theorem map_ker_projection_eq_bot_of_le_commutator
    (h : (projection (I := Fin m) (R := B)).ker ≤
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin m) B)), (projection (I := Fin m) (R := B)).ker⁆) :
    (projection (I := Fin m) (R := B)).ker.map (castSuccStab m B) = ⊥ := by
  have hmap := Subgroup.map_mono (f := castSuccStab m B) h
  rw [Subgroup.map_commutator] at hmap
  have hbot : ⁅(⊤ : Subgroup (SteinbergGroup (Fin (m + 1)) B)),
      (projection (I := Fin m) (R := B)).ker.map (castSuccStab m B)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_center_iff.mp (map_ker_projection_le_center hk) g).symm
  have htop := Subgroup.commutator_mono
    (le_top : (⊤ : Subgroup (SteinbergGroup (Fin m) B)).map (castSuccStab m B) ≤ ⊤)
    (le_refl ((projection (I := Fin m) (R := B)).ker.map (castSuccStab m B)))
  rw [hbot] at htop
  exact le_bot_iff.mp (hmap.trans htop)

/-- Element form: under the same hypothesis every stabilized `K₂` element is trivial. -/
theorem castSuccStab_eq_one_of_le_commutator
    (h : (projection (I := Fin m) (R := B)).ker ≤
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin m) B)), (projection (I := Fin m) (R := B)).ker⁆)
    {g : SteinbergGroup (Fin m) B} (hg : g ∈ (projection (I := Fin m) (R := B)).ker) :
    castSuccStab m B g = 1 := by
  have hmem : castSuccStab m B g ∈ (projection (I := Fin m) (R := B)).ker.map (castSuccStab m B) :=
    Subgroup.mem_map_of_mem _ hg
  rw [map_ker_projection_eq_bot_of_le_commutator h, Subgroup.mem_bot] at hmem
  exact hmem

end LVCentral
end Full
end GroupApproximation
