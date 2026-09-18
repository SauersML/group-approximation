import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowMat
import GroupApproximation.Meta.AxiomGuard

/-!
# Values of elementary units, stabilizations and reindexings as `suslinCongPow_m3`

Lane `bh-met-92r`.  Indices: `1 = inl 0`, `2 = inl 1`, `3 = inr ()`.

* `suslinCongPow_eU32_val`, `suslinCongPow_eU12_val`, `suslinCongPow_eU21_val`,
  `suslinCongPow_eU23_val`: `E_{ij}(c)` as a `suslinCongPow_m3`.
* `suslinCongPow_stab_val`: `diag(σ, 1)` for `σ = [[p, q], [r, s]]`.
* `suslinCongPow_e₁`, `suslinCongPow_e₂`: the reindexings placing `σ` in coordinates `(2, 3)`,
  resp. `(1, 3)` (`suslinCongPow_e₁_stab_val`, `suslinCongPow_e₂_stab_val`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- The value of an elementary unit. -/
theorem suslinCongPow_eU_val {S ι : Type*} [CommRing S] [Fintype ι] [DecidableEq ι]
    (i j : ι) (h : i ≠ j) (a : S) :
    ((elementaryUnit i j h a : (Matrix ι ι S)ˣ) : Matrix ι ι S) = 1 + Matrix.single i j a :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU_val

/-- `E₃₂(c)`. -/
theorem suslinCongPow_eU32_val {S : Type*} [CommRing S]
    (h : (Sum.inr () : Fin 2 ⊕ Unit) ≠ Sum.inl 1) (c : S) :
    ((elementaryUnit (Sum.inr ()) (Sum.inl 1) h c : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      suslinCongPow_m3 1 0 0 0 1 0 0 c 1 := by
  rw [suslinCongPow_eU_val]
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU32_val

/-- `E₁₂(c)`. -/
theorem suslinCongPow_eU12_val {S : Type*} [CommRing S]
    (h : (Sum.inl 0 : Fin 2 ⊕ Unit) ≠ Sum.inl 1) (c : S) :
    ((elementaryUnit (Sum.inl 0) (Sum.inl 1) h c : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      suslinCongPow_m3 1 c 0 0 1 0 0 0 1 := by
  rw [suslinCongPow_eU_val]
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU12_val

/-- `E₂₁(c)`. -/
theorem suslinCongPow_eU21_val {S : Type*} [CommRing S]
    (h : (Sum.inl 1 : Fin 2 ⊕ Unit) ≠ Sum.inl 0) (c : S) :
    ((elementaryUnit (Sum.inl 1) (Sum.inl 0) h c : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      suslinCongPow_m3 1 0 0 c 1 0 0 0 1 := by
  rw [suslinCongPow_eU_val]
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU21_val

/-- `E₂₃(c)`. -/
theorem suslinCongPow_eU23_val {S : Type*} [CommRing S]
    (h : (Sum.inl 1 : Fin 2 ⊕ Unit) ≠ Sum.inr ()) (c : S) :
    ((elementaryUnit (Sum.inl 1) (Sum.inr ()) h c : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      suslinCongPow_m3 1 0 0 0 1 c 0 0 1 := by
  rw [suslinCongPow_eU_val]
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU23_val

/-- `diag(σ, 1)` for `σ = [[p, q], [r, s]]`. -/
theorem suslinCongPow_stab_val {S : Type*} [CommRing S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    {p q r s : S} (hσ : (σ : Matrix (Fin 2) (Fin 2) S) = !![p, q; r, s]) :
    ((stabilizeUnit (R := S) (κ := Unit) σ : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ) :
        Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S) =
      suslinCongPow_m3 p q 0 r s 0 0 0 1 := by
  rw [stabilizeUnit_val, hσ]
  refine suslinCongPow_ext3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | rfl | simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_stab_val

/-- The value of a reindexed unit. -/
theorem suslinCongPow_reindex_apply {S ι κ : Type*} [CommRing S] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (u : (Matrix ι ι S)ˣ) (i j : κ) :
    ((elementaryReindexUnitEquiv (R := S) e u : (Matrix κ κ S)ˣ) : Matrix κ κ S) i j =
      (u : Matrix ι ι S) (e.symm i) (e.symm j) := by
  change (Matrix.reindexRingEquiv S e (u : Matrix ι ι S)) i j = _
  rw [Matrix.coe_reindexRingEquiv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_reindex_apply

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
