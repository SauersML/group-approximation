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

/-- Across a surjection with invisible kernel, the MF-closed normal subgroups
of the source are exactly the inverse images of the MF-closed normal subgroups
of the target. -/
theorem actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N : Subgroup G) [N.Normal] :
    actualCoronaMFClosure N = N ↔
      f.ker ≤ N ∧
        @actualCoronaMFClosure H _ (N.map f)
          (Subgroup.Normal.map inferInstance f hf) = N.map f := by
  letI : (N.map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hpull :=
    actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le f hf hker N
  constructor
  · intro hclosed
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxClosure : x ∈ actualCoronaMFClosure N :=
        actualCoronaMFResidual_le_actualCoronaMFClosure N (hker hx)
      rwa [hclosed] at hxClosure
    · apply le_antisymm
      · intro y hy
        obtain ⟨x, rfl⟩ := hf y
        have hx : x ∈ actualCoronaMFClosure N := by
          rw [hpull, Subgroup.mem_comap]
          exact hy
        rw [hclosed] at hx
        exact Subgroup.mem_map_of_mem f hx
      · exact le_actualCoronaMFClosure (N.map f)
  · rintro ⟨hkerN, hclosed⟩
    apply le_antisymm
    · intro x hx
      rw [hpull, Subgroup.mem_comap, hclosed] at hx
      obtain ⟨n, hn, hfn⟩ := hx
      have hxn : x * n⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfn]
        simp
      have hmem := N.mul_mem (hkerN hxn) hn
      simpa using hmem
    · exact le_actualCoronaMFClosure N

/-- Consequently, every MF quotient of the source that kills the invisible
kernel is obtained from, and only from, the corresponding MF quotient of the
target. -/
theorem isCDEOperatorMF_quotient_iff_map_of_surjective_of_ker_le
    [Countable G] [Countable H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G)
    (N : Subgroup G) [N.Normal] :
    IsCDEOperatorMF (G ⧸ N) ↔
      f.ker ≤ N ∧
        IsCDEOperatorMF (H ⧸ (N.map f : Subgroup H)) := by
  letI : (N.map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  rw [← actualCoronaMFClosure_eq_self_iff N,
    ← actualCoronaMFClosure_eq_self_iff (N.map f)]
  exact actualCoronaMFClosure_eq_self_iff_map_of_surjective_of_ker_le
    f hf hker N

end

end GroupApproximation
