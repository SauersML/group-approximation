import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.SwindleStep
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.Hsp
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRefine.Kernel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRelBrown.Main
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive

/-!
# `K₂(6, L) ≤ ⁅St_6(L), K₂(6, L)⁆` from rank-three stable triviality

Step 2 of the stability route for leaf T1b.iii (`simple_kazhdan_sofic_group.tex`, l.733-735,
`sec:questions`; Khanh, arXiv:2609.08428, Thm 5.1, Thm 5.4 and proof of Prop. 3.2).

Let `L = L_{𝔽₂}(1,2)`, `C_6 = ⁅St_6(L), K₂(6, L)⁆`, and `D² : St_4(L) → St_6(L)` the double
Leavitt refinement (`refineTwo`).  Suppose every `k ∈ K₂(3, L)` becomes trivial in some
`St_N(L)`.  Then:

* for `k ∈ K₂(3, L)`, `D²(stab k) = stab³ k` (`refineTwo_castSuccStab`), and `y = stab² k ∈ K₂(5, L)`
  is stably trivial, so `stab y ∈ C_6` by the swindle step
  (`stab_mem_commutator_of_indexMap_eq_one`);
* the relative Brown criterion (`LVRelBrown.map_ker_eq_one_of_stab`) applied to
  `Ψ = mk ∘ D² : St_4(L) → St_6(L) ⧸ C_6` shows `D²(K₂(4, L)) ≤ C_6`;
* `D²` maps `K₂(4, L)` onto `K₂(6, L)` (`LVRefine.map_ker_refineHom`), so `K₂(6, L) ≤ C_6`
  (`ker_six_le_commutator_of_stab_three`).

With `Hsp.lean` this gives `hsp` (`binaryLeavittUnits_isSuperperfect_of_stab_three`), and in
particular stable `K₂(L) = 0` gives `hsp` (`binaryLeavittUnits_isSuperperfect_of_stableK2Trivial`).
-/

namespace GroupApproximation
namespace Full
namespace LVStability

open SteinbergGroup

/-- The stabilization `castSuccStab` is padding along `Fin.castLEEmb`. -/
theorem castSuccStab_eq_indexMap {R : Type*} [Ring R] {p : ℕ} (g : SteinbergGroup (Fin p) R) :
    LVCentral.castSuccStab p R g = indexMap (Fin.castLEEmb (Nat.le_succ p)) g := by
  have he : (Fin.castSuccEmb : Fin p ↪ Fin (p + 1)) = Fin.castLEEmb (Nat.le_succ p) :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  change indexMap Fin.castSuccEmb g = _
  rw [he]

local notation "𝕃" => BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- The double refinement `D² = D_{last} ∘ D_{last} : St_4(L) → St_6(L)`
(Khanh, arXiv:2609.08428, Thm 5.4). -/
noncomputable def refineTwo : SteinbergGroup (Fin 4) 𝕃 →* SteinbergGroup (Fin 6) 𝕃 :=
  (LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4)).comp
    (LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 3))

/-- `D²` restricted to stabilized elements is stabilization. -/
theorem refineTwo_castSuccStab (g : SteinbergGroup (Fin 3) 𝕃) :
    refineTwo (LVCentral.castSuccStab 3 𝕃 g) =
      LVCentral.castSuccStab 5 𝕃 (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 g)) := by
  have h1 : LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 3)
      (LVCentral.castSuccStab 3 𝕃 g) =
      LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 g) :=
    LVRefine.refineHom_castSuccStab (BinaryLeavitt.family (ZMod 2)) 2 g
  have h2 : LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4)
      (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 g)) =
      LVCentral.castSuccStab 5 𝕃 (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 g)) :=
    LVRefine.refineHom_castSuccStab (BinaryLeavitt.family (ZMod 2)) 3
      (LVCentral.castSuccStab 3 𝕃 g)
  exact (congrArg (fun z => LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4) z)
    h1).trans h2

/-- Stable triviality of `k ∈ K₂(3, L)` passes to `stab² k ∈ K₂(5, L)`. -/
theorem stab_three_stably_trivial {k : SteinbergGroup (Fin 3) 𝕃} {N : ℕ} (hN : 3 ≤ N)
    (hkN : indexMap (Fin.castLEEmb hN) k = 1) :
    indexMap (Fin.castLEEmb (show 5 ≤ N + 5 by omega))
      (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k)) = 1 := by
  have e5 : LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k) =
      indexMap (Fin.castLEEmb (show 3 ≤ 5 by omega)) k := by
    have h1 := castSuccStab_eq_indexMap (R := 𝕃) (p := 3) k
    have h2 := castSuccStab_eq_indexMap (R := 𝕃) (p := 4) (LVCentral.castSuccStab 3 𝕃 k)
    rw [h2, h1]
    exact LVH2GL3.indexMap_castLEEmb_castLEEmb (Nat.le_succ 3) (Nat.le_succ 4) k
  have e6 : indexMap (Fin.castLEEmb (show 5 ≤ N + 5 by omega))
      (indexMap (Fin.castLEEmb (show 3 ≤ 5 by omega)) k) =
      indexMap (Fin.castLEEmb (show N ≤ N + 5 by omega)) (indexMap (Fin.castLEEmb hN) k) :=
    (LVH2GL3.indexMap_castLEEmb_castLEEmb (show 3 ≤ 5 by omega) (show 5 ≤ N + 5 by omega) k).trans
      (LVH2GL3.indexMap_castLEEmb_castLEEmb hN (show N ≤ N + 5 by omega) k).symm
  rw [e5, e6, hkN, map_one]

/-- **Relative perfectness at rank six.**  If every `k ∈ K₂(3, L)` is stably trivial, then
`K₂(6, L) ≤ ⁅St_6(L), K₂(6, L)⁆` (Khanh, Thm 5.1 relative form, with Thm 5.4). -/
theorem ker_six_le_commutator_of_stab_three
    (hstab : ∀ k : SteinbergGroup (Fin 3) 𝕃, projection k = 1 →
      ∃ (N : ℕ) (h : 3 ≤ N), indexMap (Fin.castLEEmb h) k = 1) :
    (projection (I := Fin 6) (R := 𝕃)).ker ≤
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin 6) 𝕃)), (projection (I := Fin 6) (R := 𝕃)).ker⁆ := by
  let Ψ : SteinbergGroup (Fin 4) 𝕃 →*
      SteinbergGroup (Fin 6) 𝕃 ⧸ relCommutator (projection (I := Fin 6) (R := 𝕃)) :=
    (QuotientGroup.mk' (relCommutator (projection (I := Fin 6) (R := 𝕃)))).comp refineTwo
  have hΨ : ∀ k : SteinbergGroup (Fin 3) 𝕃, projection k = 1 →
      Ψ (LVCentral.castSuccStab 3 𝕃 k) = 1 := by
    intro k hk
    obtain ⟨N, hN, hkN⟩ := hstab k hk
    have hk3 : projection (LVCentral.castSuccStab 3 𝕃 k) = 1 :=
      LVH2GL3.projection_indexMap_eq_one _ hk
    have hy : projection (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k)) = 1 :=
      LVH2GL3.projection_indexMap_eq_one _ hk3
    have hmem := stab_mem_commutator_of_indexMap_eq_one (ZMod 2) (p := 5) (q := N + 5)
      (le_refl 5) (Nat.le_add_left 5 N) hy (stab_three_stably_trivial hN hkN)
    have e6 := castSuccStab_eq_indexMap (R := 𝕃) (p := 5)
      (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k))
    have hmem' : LVCentral.castSuccStab 5 𝕃
        (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k)) ∈
        relCommutator (projection (I := Fin 6) (R := 𝕃)) := by
      rw [e6]
      exact hmem
    have hq : ((LVCentral.castSuccStab 5 𝕃
        (LVCentral.castSuccStab 4 𝕃 (LVCentral.castSuccStab 3 𝕃 k)) :
          SteinbergGroup (Fin 6) 𝕃) :
        SteinbergGroup (Fin 6) 𝕃 ⧸ relCommutator (projection (I := Fin 6) (R := 𝕃))) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem'
    have hr : Ψ (LVCentral.castSuccStab 3 𝕃 k) =
        ((refineTwo (LVCentral.castSuccStab 3 𝕃 k) : SteinbergGroup (Fin 6) 𝕃) :
          SteinbergGroup (Fin 6) 𝕃 ⧸ relCommutator (projection (I := Fin 6) (R := 𝕃))) :=
      rfl
    rw [hr, refineTwo_castSuccStab]
    exact hq
  have hK4 := LVRelBrown.map_ker_eq_one_of_stab Ψ hΨ
  have h6 : (projection (I := Fin 6) (R := 𝕃)).ker =
      (projection (I := Fin 5) (R := 𝕃)).ker.map
        (LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4)) :=
    (LVRefine.map_ker_refineHom (BinaryLeavitt.family (ZMod 2)) (by omega) (Fin.last 4)).symm
  have h5 : (projection (I := Fin 5) (R := 𝕃)).ker =
      (projection (I := Fin 4) (R := 𝕃)).ker.map
        (LVRefine.refineHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 3)) :=
    (LVRefine.map_ker_refineHom (BinaryLeavitt.family (ZMod 2)) (by omega) (Fin.last 3)).symm
  intro h hh
  rw [h6] at hh
  obtain ⟨g5, hg5, rfl⟩ := Subgroup.mem_map.1 hh
  rw [h5] at hg5
  obtain ⟨g4, hg4, rfl⟩ := Subgroup.mem_map.1 hg5
  have hq : ((refineTwo g4 : SteinbergGroup (Fin 6) 𝕃) :
      SteinbergGroup (Fin 6) 𝕃 ⧸ relCommutator (projection (I := Fin 6) (R := 𝕃))) = 1 :=
    hK4 g4 (MonoidHom.mem_ker.1 hg4)
  exact (QuotientGroup.eq_one_iff _).1 hq

/-- **`hsp` from rank-three stable triviality** (`simple_kazhdan_sofic_group.tex` l.733-735,
binder `hsp`). -/
theorem binaryLeavittUnits_isSuperperfect_of_stab_three
    (hstab : ∀ k : SteinbergGroup (Fin 3) 𝕃, projection k = 1 →
      ∃ (N : ℕ) (h : 3 ≤ N), indexMap (Fin.castLEEmb h) k = 1) :
    LVSuperperfect.IsSuperperfect (𝕃ˣ) :=
  binaryLeavittUnits_isSuperperfect_of_le_commutator (n := 6) (by omega)
    (ker_six_le_commutator_of_stab_three hstab)

/-- **`hsp` from stable `K₂(L) = 0`** (`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`;
the stable input is Ara–Brustenga–Cortiñas, `K_*(L) = 0`). -/
theorem binaryLeavittUnits_isSuperperfect_of_stableK2Trivial
    (hS : LVH2GL3.StableK2Trivial 𝕃) : LVSuperperfect.IsSuperperfect (𝕃ˣ) :=
  binaryLeavittUnits_isSuperperfect_of_stab_three fun k hk => hS 3 k hk

end LVStability
end Full
end GroupApproximation
