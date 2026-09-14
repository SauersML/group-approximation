import GroupApproximation.KOne.FieldKOneDeterminant
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-!
# `simple_kazhdan_sofic_group.tex`, marked limits: `EL₃(M_N(F₂)) = SL_{3N}(F₂)`

`simple_kazhdan_sofic_group.tex` at e80dcf20a ("Finite models"), tex 153–157:

> So $G$ and $\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$ are quotients of $\EL_3(F)$ with
> compatible generators. The equality holds since transvections generate $\SL_{3N_\ell}(\F_2)$,
> and those inside one block are commutators of those between blocks.

This module proves the displayed equality along the printed route:

* `elementaryBlockGroup_map_eq_ker_detUnits`: over any field `k` and `N ≥ 1`, block flattening
  `M₃(M_N(k)) ≅ M_{3 × N}(k)` (`elementaryBlockUnitEquiv`) carries `EL₃(M_N(k))` onto
  `SL_{3 × N}(k) = ker det`.  The two printed reasons are the two rewrites:
  - "transvections generate $\SL$": `AlgebraicK.ker_detUnits`, `ker det = EL`;
  - "those inside one block are commutators of those between blocks": `elementaryBlockGroup_map`,
    whose in-block root `(i, k) → (i, l)` is the commutator of the cross-block roots
    `(i, k) → (j, k)` and `(j, k) → (i, l)` (`elementaryUnit_mem_of_two_step`).
* `printedBlockElementarySpecialLinear`: the closed endpoint at `k = F₂`.

The index set `Fin 3 × Fin N` has `3N` elements, so `ker det` on it is the printed `SL_{3N}(F₂)`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open AlgebraicK

/-- tex 153–157 over any field: block flattening carries `EL₃(M_N(k))` onto `SL_{3 × N}(k)`. -/
theorem elementaryBlockGroup_map_eq_ker_detUnits (k : Type*) [Field k] {N : ℕ} (hN : 0 < N) :
    (elementaryGroup (Fin 3) (Matrix (Fin N) (Fin N) k)).map
        (elementaryBlockUnitEquiv (ι := Fin 3) (κ := Fin N) (R := k)).toMonoidHom =
      (detUnits (ι := Fin 3 × Fin N) (k := k)).ker := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [elementaryBlockGroup_map, ker_detUnits]

/-- **tex 153–157**, "$\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$.  The equality holds since
transvections generate $\SL_{3N_\ell}(\F_2)$, and those inside one block are commutators of those
between blocks": for every `N ≥ 1`, block flattening carries `EL₃(M_N(F₂))` onto
`SL_{3 × N}(F₂) = ker det`. -/
def PrintedBlockElementarySpecialLinear : Prop :=
  ∀ N : ℕ, 0 < N →
    (elementaryGroup (Fin 3) (Matrix (Fin N) (Fin N) (ZMod 2))).map
        (elementaryBlockUnitEquiv (ι := Fin 3) (κ := Fin N) (R := ZMod 2)).toMonoidHom =
      (detUnits (ι := Fin 3 × Fin N) (k := ZMod 2)).ker

theorem printedBlockElementarySpecialLinear : PrintedBlockElementarySpecialLinear := fun _ hN =>
  elementaryBlockGroup_map_eq_ker_detUnits (ZMod 2) hN

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.elementaryBlockGroup_map_eq_ker_detUnits
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedBlockElementarySpecialLinear
