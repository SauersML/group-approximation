import GroupApproximation.Sofic.FullMFRadicalPullback
import GroupApproximation.Sofic.MFRelationClosure

/-!
# Pullback of every MF-kernel closure

The residual pullback theorem extends from the bottom subgroup to the entire
normal-subgroup lattice.  If a surjection has kernel inside the genuine
norm-matrix-corona residual, then every MF consequence of every normal
relation set is pulled back from its image in the target.
-/

namespace GroupApproximation

noncomputable section

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- Across a surjection whose kernel is already invisible in the source, the
MF closure of every normal subgroup is the inverse image of the closure of its
image. -/
theorem actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N : Subgroup G) [N.Normal] :
    actualCoronaMFClosure N =
      (@actualCoronaMFClosure H _ (N.map f)
        (Subgroup.Normal.map inferInstance f hf)).comap f := by
  letI : (N.map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  ext x
  constructor
  · intro hx
    apply Subgroup.mem_comap.mpr
    rw [mem_actualCoronaMFClosure_iff]
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro sigma hkill
    rw [mem_actualCoronaMFClosure_iff] at hx
    exact hx X hX (sigma.comp f) (by
      intro y hy
      exact hkill (f y) ⟨y, hy, rfl⟩)
  · intro hx
    rw [Subgroup.mem_comap, mem_actualCoronaMFClosure_iff] at hx
    rw [mem_actualCoronaMFClosure_iff]
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho hkillN
    obtain ⟨sigma, hfactor⟩ :=
      UniversalFactorization.exists_comp_eq f hf rho (by
        intro y hy
        exact MonoidHom.mem_ker.mpr (hker hy X hX rho))
    have hkillMap : ∀ y ∈ N.map f, sigma y = 1 := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have heval := DFunLike.congr_fun hfactor z
      exact heval.trans (hkillN z hz)
    have hvisible := hx X hX sigma hkillMap
    have heval := DFunLike.congr_fun hfactor x
    exact heval.symm.trans hvisible

/-- Intrinsic fullness of the kernel is a sufficient hypothesis for exact
pullback of every MF closure. -/
theorem actualCoronaMFClosure_eq_comap_map_of_surjective_of_kernel_eq_top
    (f : G →* H) (hf : Function.Surjective f)
    (hker : actualCoronaMFResidual f.ker = ⊤)
    (N : Subgroup G) [N.Normal] :
    actualCoronaMFClosure N =
      (@actualCoronaMFClosure H _ (N.map f)
        (Subgroup.Normal.map inferInstance f hf)).comap f := by
  apply actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le f hf
  intro x hx
  have hx' : (⟨x, hx⟩ : f.ker) ∈ actualCoronaMFResidual f.ker := by
    rw [hker]
    exact Subgroup.mem_top _
  exact map_actualCoronaMFResidual_le f.ker.subtype
    (Subgroup.mem_map_of_mem f.ker.subtype hx')

end

end GroupApproximation
