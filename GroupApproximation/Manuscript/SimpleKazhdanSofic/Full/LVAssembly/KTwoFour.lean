import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRelBrown.Main
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.StabKills
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel

/-!
# `K₂(4, L) = ⊥` from the coinvariant condition at rank three

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is the last step of
Khanh (arXiv:2609.08428), Thm 5.1, over `L = L_{𝔽₂}(1,2)`.

Suppose `K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆`.  Then stabilization kills `K₂(3, L)` inside `St_4(L)`
(`LVCentral.castSuccStab_eq_one_of_le_commutator`).  The relative rank-four Brown criterion
`LVRelBrown.map_ker_eq_one_of_stab`, applied with `Ψ = id`, then gives `K₂(4, L) = ⊥`.

* `k2Four_eq_bot_of_le_commutator`: `K₂(3, L) ≤ ⁅⊤, K₂(3, L)⁆ → K₂(4, L) = ⊥`.
-/

namespace GroupApproximation.Full.LVAssembly

/-- **`K₂(4, L) = ⊥` from `K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆`** (Khanh, Thm 5.1; tex l.733-735).
Stabilization kills `K₂(3, L)` in `St_4(L)`, and the relative Brown criterion with `Ψ = id`
kills `K₂(4, L)`. -/
theorem k2Four_eq_bot_of_le_commutator
    (h : (GroupApproximation.SteinbergGroup.projection (I := Fin 3) (R := BinL)).ker ≤
      ⁅(⊤ : Subgroup (GroupApproximation.SteinbergGroup (Fin 3) BinL)),
        (GroupApproximation.SteinbergGroup.projection (I := Fin 3) (R := BinL)).ker⁆) :
    GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin 4) BinL = ⊥ := by
  have hid : ∀ k : GroupApproximation.SteinbergGroup (Fin 4) BinL,
      GroupApproximation.SteinbergGroup.projection k = 1 →
        MonoidHom.id (GroupApproximation.SteinbergGroup (Fin 4) BinL) k = 1 :=
    GroupApproximation.Full.LVRelBrown.map_ker_eq_one_of_stab
      (MonoidHom.id (GroupApproximation.SteinbergGroup (Fin 4) BinL))
      (fun k hk => by
        rw [MonoidHom.id_apply]
        exact GroupApproximation.Full.LVCentral.castSuccStab_eq_one_of_le_commutator h
          (MonoidHom.mem_ker.mpr hk))
  refine (Subgroup.eq_bot_iff_forall _).mpr fun k hk => ?_
  exact hid k hk

end GroupApproximation.Full.LVAssembly
