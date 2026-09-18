import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourIntertwine
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# The used `K₂` statement descends from rank five to rank four (lane sk-leavitt-25)

Let `L = L_{𝔽₂}(1,2)` (`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)`) and
`D = refineHom (BinaryLeavitt.family (ZMod 2)) 3 : St_4(L) → St_5(L)`.

`LeavittK2UsedStatement` (lane sk-leavitt-24) says every `k ∈ K₂(5, L)` dies in some `St_N(L)`.
This file proves it from the rank-four instance `LeavittK2UsedRankFourStatement`.

## Route

* `LeavittFP.binaryLeavitt_K2_five_eq_map_four`: `K₂(5, L) = D(K₂(4, L))`, unconditionally.
  So `k = D w` with `w ∈ K₂(4, L)`.
* The rank-four statement gives `N ≥ 4` with `pad_{4 → N} w = 1`.
* `usedRankFour_pad_refine_eq_one` (from the intertwining identity
  `pad_{5 → N+1} ∘ D = indexMap σ ∘ refineHom 3 ∘ pad_{4 → N}`) gives `pad_{5 → N+1} (D w) = 1`.

## Truth check

`LeavittK2UsedRankFourStatement` is true: `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428v1, Thm 5.4 at
`r = 4`), so `N = 4` works (`leavittK2UsedRankFour_of_rankFourInjective`).  It is not proved in Lean.

## Strength

The rank-five statement follows from it with an unconditional proof (`leavittK2Used_of_rankFour`).
The converse is not proved: running the intertwining backwards would need `refineHom` to be
injective at rank `N`, which is itself `K₂` content.  So the remaining gap sits at rank four,
the rank to which `LeavittFP.K2RankFourEndpoints` already reduces the other `K₂` gaps.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- **The rank-four used statement.**  Every `k ∈ K₂(4, L_{𝔽₂}(1,2))` becomes trivial in some
`St_N(L_{𝔽₂}(1,2))`, `4 ≤ N`, under the relabelling along `Fin.castLE`.

*Why it is true.*  `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428v1, Thm 5.4), see
`leavittK2UsedRankFour_of_rankFourInjective`.  Not proved in Lean. -/
def LeavittK2UsedRankFourStatement : Prop :=
  ∀ k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 4)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
    ∃ (N : ℕ) (h : 4 ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.LeavittK2UsedRankFourStatement

/-- **The reduction.**  The rank-four used statement implies the rank-five used statement. -/
theorem leavittK2Used_of_rankFour (h4 : LeavittK2UsedRankFourStatement) :
    LeavittK2UsedStatement := by
  intro k hk
  have hle : GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin (4 + 1))
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
      (GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 4)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
        (LeavittFP.refineHom (GroupApproximation.BinaryLeavitt.family (ZMod 2)) (3 : Fin 4)) :=
    le_of_eq LeavittFP.binaryLeavitt_K2_five_eq_map_four.symm
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (hle hk)
  obtain ⟨N, hN, hwN⟩ := h4 w hw
  exact ⟨N + 1, Nat.add_le_add_right hN 1,
    usedRankFour_pad_refine_eq_one (GroupApproximation.BinaryLeavitt.family (ZMod 2))
      (3 : Fin 4) hN hwN⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_rankFour

/-- **Truth check.**  `K₂(4, L) = ⊥` gives the rank-four used statement with `N = 4`. -/
theorem leavittK2UsedRankFour_of_rankFourInjective
    (h : GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement) :
    LeavittK2UsedRankFourStatement := by
  have h' : GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 4)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ := h
  intro k hk
  refine ⟨4, le_rfl, ?_⟩
  rw [(Subgroup.eq_bot_iff_forall _).mp h' k hk, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2UsedRankFour_of_rankFourInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
