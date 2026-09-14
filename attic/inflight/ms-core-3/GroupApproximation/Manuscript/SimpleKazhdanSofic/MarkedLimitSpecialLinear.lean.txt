import GroupApproximation.KOne.FieldKOneDeterminant
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-!
# `simple_kazhdan_sofic_group.tex`, marked limits: `EL_n(M_N(F₂)) = SL_{nN}(F₂)`

`simple_kazhdan_sofic_group.tex` at e80dcf20a ("Finite models"), tex 153–157:

> So $G$ and $\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$ are quotients of $\EL_3(F)$ with
> compatible generators. The equality holds since transvections generate $\SL_{3N_\ell}(\F_2)$,
> and those inside one block are commutators of those between blocks.

`thm:main` states the marked limits for `EL_n`, every `n ≥ 3`, so this module proves the displayed
equality at that generality, along the printed route:

* `elementaryBlockGroup_map_eq_ker_detUnits`: over any field `k`, for `n ≥ 2` and `N ≥ 1`, block
  flattening `M_n(M_N(k)) ≅ M_{n × N}(k)` (`elementaryBlockUnitEquiv`) carries `EL_n(M_N(k))` onto
  `SL_{n × N}(k) = ker det`.  The two printed reasons are the two rewrites:
  - "transvections generate $\SL$": `AlgebraicK.ker_detUnits`, `ker det = EL`;
  - "those inside one block are commutators of those between blocks": `elementaryBlockGroup_map`,
    whose in-block root `(i, k) → (i, l)` is the commutator of the cross-block roots
    `(i, k) → (j, k)` and `(j, k) → (i, l)` (`elementaryUnit_mem_of_two_step`).
* `printedBlockElementarySpecialLinear`: the closed endpoint at `k = F₂`, for every `n ≥ 3`.

The index set `Fin n × Fin N` has `nN` elements, so `ker det` on it is the printed `SL_{nN}(F₂)`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open AlgebraicK

/-- tex 153–157 over any field: block flattening carries `EL_n(M_N(k))` onto `SL_{n × N}(k)`,
for `n ≥ 2` and `N ≥ 1`. -/
theorem elementaryBlockGroup_map_eq_ker_detUnits (k : Type*) [Field k] {n N : ℕ} (hn : 2 ≤ n)
    (hN : 0 < N) :
    (elementaryGroup (Fin n) (Matrix (Fin N) (Fin N) k)).map
        (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin N) (R := k)).toMonoidHom =
      (detUnits (ι := Fin n × Fin N) (k := k)).ker := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [elementaryBlockGroup_map, ker_detUnits]

/-- **tex 153–157**, "$\EL_3(M_{N_\ell}(\F_2))=\SL_{3N_\ell}(\F_2)$.  The equality holds since
transvections generate $\SL_{3N_\ell}(\F_2)$, and those inside one block are commutators of those
between blocks", at the generality of `thm:main`: for every `n ≥ 3` and `N ≥ 1`, block flattening
carries `EL_n(M_N(F₂))` onto `SL_{n × N}(F₂) = ker det`. -/
def PrintedBlockElementarySpecialLinear : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ N : ℕ, 0 < N →
    (elementaryGroup (Fin n) (Matrix (Fin N) (Fin N) (ZMod 2))).map
        (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin N) (R := ZMod 2)).toMonoidHom =
      (detUnits (ι := Fin n × Fin N) (k := ZMod 2)).ker

theorem printedBlockElementarySpecialLinear : PrintedBlockElementarySpecialLinear :=
  fun _ hn _ hN => elementaryBlockGroup_map_eq_ker_detUnits (ZMod 2) (by omega) hN

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.elementaryBlockGroup_map_eq_ker_detUnits
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedBlockElementarySpecialLinear
