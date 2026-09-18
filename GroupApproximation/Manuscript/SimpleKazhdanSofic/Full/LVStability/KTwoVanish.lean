import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.RelSix
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Endpoint

/-!
# `K₂(m, L) = ⊥` for `m ≥ 4`, and injective stability (work order W2)

Step 4 of the stability route for leaf T1b.iii (`simple_kazhdan_sofic_group.tex`, l.733-735,
`sec:questions`; Khanh, arXiv:2609.08428, Lemma 5.2, Thm 5.1, Thm 5.4).

Let `L = L_{𝔽₂}(1,2)`.

* `castSuccStab_eq_one_of_isSuperperfect`: `hsp` kills `stab (K₂(3, L))`.  This combines padded
  centrality (`LVCentral.binaryLeavittPaddedCentralThree`) with
  `LeavittK2.stabKernelThreeTrivial_of_paddedCentral_of_superperfect`.
* `ker_four_eq_bot_of_isSuperperfect`: the relative Brown criterion with `Ψ = id` gives
  `K₂(4, L) = ⊥`.
* `ker_eq_bot_of_isSuperperfect`: Leavitt refinement maps `K₂(m)` onto `K₂(m+1)`, so
  `K₂(m, L) = ⊥` for all `m ≥ 4`.
* `binaryLeavitt_k2StabInjective_of_stab_three` and
  `binaryLeavitt_k2StabInjective_of_stableK2Trivial`: work order W2 from rank-three stable
  triviality of `K₂`, and in particular from stable `K₂(L) = 0`.

This file does not import `LVAssembly.KTwoFour`.
-/

namespace GroupApproximation
namespace Full
namespace LVStability

open SteinbergGroup

local notation "𝕃" => BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- `hsp` makes stabilization `St_3(L) → St_4(L)` kill `K₂(3, L)`. -/
theorem castSuccStab_eq_one_of_isSuperperfect (hsp : LVSuperperfect.IsSuperperfect (𝕃ˣ))
    (k : SteinbergGroup (Fin 3) 𝕃) (hk : projection k = 1) :
    LVCentral.castSuccStab 3 𝕃 k = 1 := by
  have hbot : (projection (I := Fin 3) (R := 𝕃)).ker.map (LVCentral.castSuccStab 3 𝕃) = ⊥ :=
    Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivial_of_paddedCentral_of_superperfect
      LVCentral.binaryLeavittPaddedCentralThree hsp
  have hmem : LVCentral.castSuccStab 3 𝕃 k ∈
      (projection (I := Fin 3) (R := 𝕃)).ker.map (LVCentral.castSuccStab 3 𝕃) :=
    Subgroup.mem_map_of_mem _ (MonoidHom.mem_ker.2 hk)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

/-- `hsp` gives `K₂(4, L) = ⊥` (relative Brown criterion with `Ψ = id`; Khanh, Thm 5.1). -/
theorem ker_four_eq_bot_of_isSuperperfect (hsp : LVSuperperfect.IsSuperperfect (𝕃ˣ)) :
    (projection (I := Fin 4) (R := 𝕃)).ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  intro g hg
  have h := LVRelBrown.map_ker_eq_one_of_stab (MonoidHom.id (SteinbergGroup (Fin 4) 𝕃))
    (fun k hk => castSuccStab_eq_one_of_isSuperperfect hsp k hk) g (MonoidHom.mem_ker.1 hg)
  exact h

/-- `hsp` gives `K₂(m, L) = ⊥` for every `m ≥ 4` (Khanh, Thm 5.4). -/
theorem ker_eq_bot_of_isSuperperfect (hsp : LVSuperperfect.IsSuperperfect (𝕃ˣ)) {m : ℕ}
    (hm : 4 ≤ m) : (projection (I := Fin m) (R := 𝕃)).ker = ⊥ := by
  induction m, hm using Nat.le_induction with
  | base => exact ker_four_eq_bot_of_isSuperperfect hsp
  | succ n hn ih =>
    have hmap := LVRefine.map_ker_refineHom (BinaryLeavitt.family (ZMod 2)) (n := n)
      (by omega) ⟨0, by omega⟩
    rw [← hmap, ih, Subgroup.map_bot]

/-- `hsp` gives injective stability `K₂(m, L) → K₂(m+1, L)` for `m ≥ 4`. -/
theorem binaryLeavitt_k2StabInjective_of_isSuperperfect
    (hsp : LVSuperperfect.IsSuperperfect (𝕃ˣ)) {m : ℕ} (hm : 4 ≤ m) :
    LVH2GL3.K2StabInjective 𝕃 m :=
  LVH2GL3.k2StabInjective_of_ker_eq_bot (ker_eq_bot_of_isSuperperfect hsp hm)

/-- **Work order W2 from rank-three stable triviality** (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii): if every `k ∈ K₂(3, L)` dies in some `St_N(L)`, then
`K₂(m, L) → K₂(m+1, L)` is injective for `m ≥ 5`. -/
theorem binaryLeavitt_k2StabInjective_of_stab_three
    (hstab : ∀ k : SteinbergGroup (Fin 3) 𝕃, projection k = 1 →
      ∃ (N : ℕ) (h : 3 ≤ N), indexMap (Fin.castLEEmb h) k = 1)
    {m : ℕ} (hm : 5 ≤ m) : LVH2GL3.K2StabInjective 𝕃 m :=
  binaryLeavitt_k2StabInjective_of_isSuperperfect
    (binaryLeavittUnits_isSuperperfect_of_stab_three hstab) (by omega)

/-- **Work order W2 from stable `K₂(L) = 0`** (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii; stable input: work order W1). -/
theorem binaryLeavitt_k2StabInjective_of_stableK2Trivial (hS : LVH2GL3.StableK2Trivial 𝕃)
    {m : ℕ} (hm : 5 ≤ m) : LVH2GL3.K2StabInjective 𝕃 m :=
  binaryLeavitt_k2StabInjective_of_stab_three (fun k hk => hS 3 k hk) hm

end LVStability
end Full
end GroupApproximation
