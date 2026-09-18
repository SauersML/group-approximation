import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.Compress
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.Lifts

/-!
# The swindle step: stably trivial `K₂` elements become relative commutators

Stability step S0' of leaf T1b.iii (`simple_kazhdan_sofic_group.tex`, l.733-735,
`sec:questions`; Khanh, arXiv:2609.08428, proof of Prop. 3.2).

Let `L = L_k(1,2)`, `π_p : St_p(L) → GL_p(L)` and `C_p = ⁅St_p(L), ker π_p⁆`.  Write
`j : St_p(L) → St_{p+1}(L)` for identity padding and `κ̃` for compression of coordinate `0`
(`Compress.lean`).  Using Kervaire lifts of the leaf isomorphism `δ : GL_{p+1}(L) ≅ GL_p(L)`
into `St_p(L) ⧸ C_p` (and of its inverse into `St_{p+1}(L) ⧸ C_{p+1}`) we prove:

* `indexMap_mem_relCommutator_iff`: for `p ≥ 5`, `j y ∈ C_{p+1} ↔ κ̃ y ∈ C_p`;
* `steinbergCompress_mem_relCommutator_of_twice`: for `y ∈ K₂(p)`, `κ̃ κ̃ y ∈ C_p → κ̃ y ∈ C_p`;
* `stab_mem_commutator_of_indexMap_eq_one`: if `y ∈ K₂(p)`, `p ≥ 5`, and the padding of `y`
  to some `St_q(L)` is trivial, then `j y ∈ ⁅St_{p+1}(L), K₂(p+1)⁆`.
-/

namespace GroupApproximation
namespace Full
namespace LVStability

open SteinbergGroup

section Generic

/-- A lift `D` of `φ ∘ π` through `quotHom π'` kills `⁅G, ker π⁆`. -/
theorem lift_relCommutator_le_ker {G H G' H' : Type*} [Group G] [Group H] [Group G']
    [Group H'] (π : G →* H) (π' : G' →* H') (φ : H →* H') (D : G →* G' ⧸ relCommutator π')
    (hD : (quotHom π').comp D = φ.comp π) : relCommutator π ≤ D.ker := by
  refine commutator_ker_le_ker π D ?_
  intro y hy
  apply quotHom_ker_le_center π'
  rw [MonoidHom.mem_ker]
  have hDy : quotHom π' (D y) = φ (π y) := DFunLike.congr_fun hD y
  rw [hDy, MonoidHom.mem_ker.1 hy, map_one]

end Generic

section Leavitt

variable (k : Type) [Field k]

/-- **Compression equivalence.** For `p ≥ 5` and `y ∈ St_p(L)`:
`j y ∈ ⁅St_{p+1}, ker π_{p+1}⁆ ↔ κ̃ y ∈ ⁅St_p, ker π_p⁆`. -/
theorem indexMap_mem_relCommutator_iff {p : ℕ} (hp : 5 ≤ p)
    (y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
    indexMap (Fin.castLEEmb (Nat.le_succ p)) y ∈
        relCommutator (LVEGen.steinbergToGL k (p + 1)) ↔
      steinbergCompress (BinaryLeavitt.family k) p y ∈
        relCommutator (LVEGen.steinbergToGL k p) := by
  have hp0 : 0 < p := by omega
  haveI : Group.IsPerfect (SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :=
    SteinbergGroup.fin_isPerfect (by omega)
  haveI : Group.IsPerfect
      (SteinbergGroup (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k)) :=
    SteinbergGroup.fin_isPerfect (by omega)
  obtain ⟨D, hD⟩ := exists_lift_quotHom (n := p + 1) (by omega) (LVEGen.steinbergToGL k p)
    (LVEGen.steinbergToGL_surjective k (by omega))
    ((compressUnits (BinaryLeavitt.family k) hp0).comp (LVEGen.steinbergToGL k (p + 1)))
  obtain ⟨E, hE⟩ := exists_lift_quotHom (n := p) hp (LVEGen.steinbergToGL k (p + 1))
    (LVEGen.steinbergToGL_surjective k (by omega))
    ((expandUnits (BinaryLeavitt.family k) hp0).comp (LVEGen.steinbergToGL k p))
  have hDker : relCommutator (LVEGen.steinbergToGL k (p + 1)) ≤ D.ker :=
    lift_relCommutator_le_ker _ _ _ D hD
  have hEker : relCommutator (LVEGen.steinbergToGL k p) ≤ E.ker :=
    lift_relCommutator_le_ker _ _ _ E hE
  -- `D ∘ j = mk ∘ κ̃`, by uniqueness of lifts out of the perfect group `St_p(L)`.
  have hDj : ∀ z : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k),
      D (indexMap (Fin.castLEEmb (Nat.le_succ p)) z) =
        ((steinbergCompress (BinaryLeavitt.family k) p z :
            SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
            relCommutator (LVEGen.steinbergToGL k p)) := by
    have hh : D.comp (indexMap (Fin.castLEEmb (Nat.le_succ p))) =
        (QuotientGroup.mk' (relCommutator (LVEGen.steinbergToGL k p))).comp
          (steinbergCompress (BinaryLeavitt.family k) p) := by
      apply hom_eq_of_quotHom_comp_eq (LVEGen.steinbergToGL k p)
      refine MonoidHom.ext fun z => ?_
      have hDz : quotHom (LVEGen.steinbergToGL k p)
            (D (indexMap (Fin.castLEEmb (Nat.le_succ p)) z)) =
          compressUnits (BinaryLeavitt.family k) hp0
            (LVEGen.steinbergToGL k (p + 1) (indexMap (Fin.castLEEmb (Nat.le_succ p)) z)) :=
        DFunLike.congr_fun hD (indexMap (Fin.castLEEmb (Nat.le_succ p)) z)
      change quotHom (LVEGen.steinbergToGL k p)
          (D (indexMap (Fin.castLEEmb (Nat.le_succ p)) z)) =
        LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p z)
      rw [hDz]
      exact compressUnits_steinbergToGL_indexMap k hp0 z
    exact fun z => DFunLike.congr_fun hh z
  -- `Ē ∘ D = mk`, by uniqueness of lifts out of the perfect group `St_{p+1}(L)`.
  have hED : ∀ z : SteinbergGroup (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k),
      QuotientGroup.lift (relCommutator (LVEGen.steinbergToGL k p)) E hEker (D z) =
        (z : SteinbergGroup (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
          relCommutator (LVEGen.steinbergToGL k (p + 1))) := by
    have hh : (QuotientGroup.lift (relCommutator (LVEGen.steinbergToGL k p)) E hEker).comp D =
        QuotientGroup.mk' (relCommutator (LVEGen.steinbergToGL k (p + 1))) := by
      apply hom_eq_of_quotHom_comp_eq (LVEGen.steinbergToGL k (p + 1))
      refine MonoidHom.ext fun z => ?_
      obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (D z)
      have hDz : quotHom (LVEGen.steinbergToGL k p) (D z) =
          compressUnits (BinaryLeavitt.family k) hp0 (LVEGen.steinbergToGL k (p + 1) z) :=
        DFunLike.congr_fun hD z
      have hEw : quotHom (LVEGen.steinbergToGL k (p + 1)) (E w) =
          expandUnits (BinaryLeavitt.family k) hp0 (LVEGen.steinbergToGL k p w) :=
        DFunLike.congr_fun hE w
      rw [← hw, quotHom_mk] at hDz
      change quotHom (LVEGen.steinbergToGL k (p + 1))
          (QuotientGroup.lift (relCommutator (LVEGen.steinbergToGL k p)) E hEker (D z)) =
        LVEGen.steinbergToGL k (p + 1) z
      rw [← hw, QuotientGroup.lift_mk, hEw, hDz, expandUnits_compressUnits]
    exact fun z => DFunLike.congr_fun hh z
  constructor
  · intro hmem
    have h1 : D (indexMap (Fin.castLEEmb (Nat.le_succ p)) y) = 1 :=
      MonoidHom.mem_ker.1 (hDker hmem)
    rw [hDj y] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  · intro hmem
    have h1 : ((steinbergCompress (BinaryLeavitt.family k) p y :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
        SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
          relCommutator (LVEGen.steinbergToGL k p)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    have h2 := hED (indexMap (Fin.castLEEmb (Nat.le_succ p)) y)
    rw [hDj y, h1, map_one] at h2
    exact (QuotientGroup.eq_one_iff _).1 h2.symm

/-- **Idempotence modulo the relative commutator.** For `y ∈ K₂(p, L)`, `p ≥ 3`:
if `κ̃ (κ̃ y) ∈ ⁅St_p, ker π_p⁆` then `κ̃ y ∈ ⁅St_p, ker π_p⁆`. -/
theorem steinbergCompress_mem_relCommutator_of_twice {p : ℕ} (hp : 3 ≤ p)
    {y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)} (hy : projection y = 1)
    (h2 : steinbergCompress (BinaryLeavitt.family k) p
        (steinbergCompress (BinaryLeavitt.family k) p y) ∈
      relCommutator (LVEGen.steinbergToGL k p)) :
    steinbergCompress (BinaryLeavitt.family k) p y ∈
      relCommutator (LVEGen.steinbergToGL k p) := by
  haveI : Group.IsPerfect (SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :=
    SteinbergGroup.fin_isPerfect hp
  obtain ⟨g', hg'⟩ := quotHom_surjective (LVEGen.steinbergToGL k p)
    (LVEGen.steinbergToGL_surjective k (by omega))
    (diagMatrixUnit (coordConjUnit (BinaryLeavitt.family k)))
  have hconj : (QuotientGroup.mk' (relCommutator (LVEGen.steinbergToGL k p))).comp
        ((steinbergCompress (BinaryLeavitt.family k) p).comp
          (steinbergCompress (BinaryLeavitt.family k) p)) =
      (MulAut.conj g').toMonoidHom.comp
        ((QuotientGroup.mk' (relCommutator (LVEGen.steinbergToGL k p))).comp
          (steinbergCompress (BinaryLeavitt.family k) p)) := by
    apply hom_eq_of_quotHom_comp_eq (LVEGen.steinbergToGL k p)
    refine MonoidHom.ext fun z => ?_
    change LVEGen.steinbergToGL k p (steinbergCompress (BinaryLeavitt.family k) p
        (steinbergCompress (BinaryLeavitt.family k) p z)) =
      quotHom (LVEGen.steinbergToGL k p)
        (g' * ((steinbergCompress (BinaryLeavitt.family k) p z :
            SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
            relCommutator (LVEGen.steinbergToGL k p)) * g'⁻¹)
    rw [map_mul, map_mul, map_inv, hg', quotHom_mk]
    exact steinbergToGL_steinbergCompress_steinbergCompress k z
  have hc := mk_mem_center_of_mem_ker (LVEGen.steinbergToGL k p)
    (MonoidHom.mem_ker.2 (steinbergToGL_steinbergCompress_eq_one k (by omega) hy))
  have heq : ((steinbergCompress (BinaryLeavitt.family k) p
          (steinbergCompress (BinaryLeavitt.family k) p y) :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
        SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
          relCommutator (LVEGen.steinbergToGL k p)) =
      g' * ((steinbergCompress (BinaryLeavitt.family k) p y :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
        SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
          relCommutator (LVEGen.steinbergToGL k p)) * g'⁻¹ :=
    DFunLike.congr_fun hconj y
  rw [Subgroup.mem_center_iff.1 hc g', mul_inv_cancel_right] at heq
  have h1 : ((steinbergCompress (BinaryLeavitt.family k) p
          (steinbergCompress (BinaryLeavitt.family k) p y) :
          SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) :
        SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k) ⧸
          relCommutator (LVEGen.steinbergToGL k p)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 h2
  rw [heq] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem indexMap_succ_mem_of_self {p : ℕ}
    (y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)) (h : p ≤ p)
    (hyd : indexMap (Fin.castLEEmb h) y = 1) :
    indexMap (Fin.castLEEmb (Nat.le_succ p)) y ∈
      relCommutator (LVEGen.steinbergToGL k (p + 1)) := by
  rw [LVH2GL3.indexMap_castLEEmb_self] at hyd
  rw [hyd, map_one]
  exact Subgroup.one_mem _

/-- Induction on the stabilization distance `d` with `q ≤ p + d`. -/
theorem indexMap_succ_mem_relCommutator_aux (d : ℕ) :
    ∀ p : ℕ, 5 ≤ p → ∀ q : ℕ, ∀ h : p ≤ q, q ≤ p + d →
      ∀ y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k), projection y = 1 →
        indexMap (Fin.castLEEmb h) y = 1 →
          indexMap (Fin.castLEEmb (Nat.le_succ p)) y ∈
            relCommutator (LVEGen.steinbergToGL k (p + 1)) := by
  induction d with
  | zero =>
      intro p _ q h hq y _ hyd
      have hqp : p = q := by omega
      subst hqp
      exact indexMap_succ_mem_of_self k y h hyd
  | succ d ih =>
      intro p hp q h hq y hy hyd
      rcases Nat.eq_or_lt_of_le h with hqp | hlt
      · subst hqp
        exact indexMap_succ_mem_of_self k y h hyd
      · have h' : p + 1 ≤ q := hlt
        have hz : projection (indexMap (Fin.castLEEmb (Nat.le_succ p)) y) = 1 :=
          LVH2GL3.projection_indexMap_eq_one _ hy
        have hzd : indexMap (Fin.castLEEmb h')
            (indexMap (Fin.castLEEmb (Nat.le_succ p)) y) = 1 := by
          rw [LVH2GL3.indexMap_castLEEmb_castLEEmb]
          exact hyd
        have h1 := ih (p + 1) (by omega) q h' (by omega) _ hz hzd
        rw [indexMap_mem_relCommutator_iff k (p := p + 1) (by omega),
          steinbergCompress_indexMap_castLE, indexMap_mem_relCommutator_iff k hp] at h1
        exact (indexMap_mem_relCommutator_iff k hp y).2
          (steinbergCompress_mem_relCommutator_of_twice k (by omega) hy h1)

/-- **Swindle step S0'.** If `y ∈ K₂(p, L)` with `p ≥ 5` becomes trivial in `St_q(L)` for
some `q ≥ p`, then its padding to `St_{p+1}(L)` lies in `⁅St_{p+1}(L), K₂(p+1, L)⁆`. -/
theorem stab_mem_commutator_of_indexMap_eq_one {p q : ℕ} (hp : 5 ≤ p) (h : p ≤ q)
    {y : SteinbergGroup (Fin p) (BinaryLeavitt.BinaryLeavittAlgebra k)} (hy : projection y = 1)
    (hyd : indexMap (Fin.castLEEmb h) y = 1) :
    indexMap (Fin.castLEEmb (Nat.le_succ p)) y ∈
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin (p + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k))),
        (projection (I := Fin (p + 1)) (R := BinaryLeavitt.BinaryLeavittAlgebra k)).ker⁆ := by
  have hmem := indexMap_succ_mem_relCommutator_aux k (q - p) p hp q h (by omega) y hy hyd
  rw [← LVEGen.steinbergToGL_ker k (p + 1)]
  exact hmem

end Leavitt

end LVStability
end Full
end GroupApproximation
