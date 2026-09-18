import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChange
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
import GroupApproximation.Leavitt.AryEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Base change `K₂(𝔽₂) → K₂(C_2(𝔽₂))`: the conjugation form

Lane `sk-leavitt-22`.  Write `C = C_2(𝔽₂)` and `ι = algebraMap 𝔽₂ C`.

**Truth check.**  `CohnBaseChangeK2Statement` is true.  Ara–Brustenga–Cortiñas show that
`ι` is a `K`-equivalence, and stable `K₂(𝔽₂) = 0`, so stable `K₂(C) = 0`.  Padding
commutes with `ι`, and `K₂` is the filtered colimit of the `K₂(n, -)`.  Hence every
`k ∈ K₂(n, C)` pads to `1 = ι 1`, and `y = 1` works.

**Not closed in Lean.**  Every known proof of the degree-two `K`-equivalence uses
universal-localisation `K`-theory, or a Gersten–Waldhausen resolution of `C` over the free
algebra.  The finite-stage routes checked on paper fail:
* `(p)` is the only nontrivial two-sided ideal, so relative sequences reduce to
  `K₂(L)` (circular);
* the degree-zero part of `C` is ultramatricial.  The Pimsner–Voiculescu step that
  follows is research-level;
* the Fock representation `C ↪ End(V)` is flasque and gives no surjectivity;
* the isometry corner `x ↦ e x e*` is inner, via `W = [[e, 1 - e e*], [0, e*]]`, but
  there is no trace and no retraction to push `k` back to `𝔽₂`;
* the matrix of corners `[[e* x e, e* x f], [f* x e, f* x f]]` is multiplicative only
  modulo `(p)`.

**Isolated gap.**  `CohnBaseChangeConjStatement` relaxes the target in two ways:
1. it drops the conjunct `y ∈ K₂(N, 𝔽₂)`;
2. it asks for `ι y = pad k` only up to conjugation in `St_N(C)`.

This is the freedom that Karoubi-type rotation arguments produce naturally.

The target implies it with `g = 1`, so as a statement it is syntactically weaker; see
`conj_of_cohnBaseChange`.  Its sufficiency, `cohnBaseChange_of_conj`, is proved in two steps:
* conjugation is absorbed by padding once, because stabilised `K₂` is central in
  `St_{N+1}` (`map_stab_K2_le_center`);
* the `K₂` conjunct follows from injectivity of `E_N(𝔽₂) → E_N(C)` (`C ≠ 0` since `p ≠ 0`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

/-- **Isolated gap (lane `sk-leavitt-22`).**  After stabilisation, every `k ∈ K₂(n, C_2(𝔽₂))`
is conjugate in `St_N(C_2(𝔽₂))` to the image of a Steinberg element over `𝔽₂`. -/
def CohnBaseChangeConjStatement : Prop :=
  ∀ (n : ℕ) (k : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n) (CohnTwo (ZMod 2)) →
    ∃ (N : ℕ) (h : n ≤ N) (y : GroupApproximation.SteinbergGroup (Fin N) (ZMod 2))
      (g : GroupApproximation.SteinbergGroup (Fin N) (CohnTwo (ZMod 2))),
      GroupApproximation.SteinbergGroup.ringMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2))) y =
        g * GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k * g⁻¹

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnBaseChangeConjStatement

/-- The conjugation form suffices for the base-change statement. -/
theorem cohnBaseChange_of_conj (hC : CohnBaseChangeConjStatement) :
    CohnBaseChangeK2Statement := by
  intro n k hk
  obtain ⟨N, hN, y, g, hy⟩ := hC n k hk
  haveI : Nontrivial (CohnTwo (ZMod 2)) :=
    nontrivial_of_ne _ _ (CohnTwo.data_p_ne_zero (ZMod 2))
  have hinj : Function.Injective (algebraMap (ZMod 2) (CohnTwo (ZMod 2))) :=
    RingHom.injective _
  have hc : indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) (indexMap (Fin.castLEEmb hN) k) ∈
      Subgroup.center (St (N + 1) (CohnTwo (ZMod 2))) :=
    map_stab_K2_le_center (R := CohnTwo (ZMod 2)) (n := N)
      (Subgroup.mem_map_of_mem (stab N (CohnTwo (ZMod 2)))
        (indexMap_mem_K2 (Fin.castLEEmb hN) hk))
  have hc' := Subgroup.mem_center_iff.mp hc
    (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) g)
  have hmain : ringMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2)))
      (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y) =
      indexMap (Fin.castLEEmb (hN.trans (Nat.le_add_right N 1))) k := by
    rw [← CohnTwo.indexMap_castLE_ringMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2)))
        (Nat.le_add_right N 1) y, hy, map_mul, map_mul, map_inv, hc', mul_inv_cancel_right,
      CohnTwo.indexMap_castLE_castLE hN (Nat.le_add_right N 1) k]
  have hK : projection (ringMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2)))
      (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y)) = 1 := by
    rw [hmain]
    exact (mem_K2_iff _).mp (indexMap_mem_K2 (Fin.castLEEmb (hN.trans (Nat.le_add_right N 1))) hk)
  rw [projection_ringMap] at hK
  refine ⟨N + 1, hN.trans (Nat.le_add_right N 1),
    indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y, ?_, hmain⟩
  rw [mem_K2_iff]
  have h1 : elementaryGroupMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2)))
      (projection (indexMap (Fin.castLEEmb (Nat.le_add_right N 1)) y)) =
      elementaryGroupMap (algebraMap (ZMod 2) (CohnTwo (ZMod 2))) 1 := by
    rw [hK, map_one]
  exact elementaryGroupMap_injective _ hinj h1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnBaseChange_of_conj

/-- The base-change statement implies its conjugation form (take `g = 1`). -/
theorem conj_of_cohnBaseChange (hB : CohnBaseChangeK2Statement) :
    CohnBaseChangeConjStatement := by
  intro n k hk
  obtain ⟨N, hN, y, _, hy⟩ := hB n k hk
  exact ⟨N, hN, y, 1, by rw [hy, one_mul, inv_one, mul_one]⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.conj_of_cohnBaseChange

/-- Stable `K₂(C_2(𝔽₂))` vanishes, given the conjugation form and stable `K₂(𝔽₂) = 0`. -/
theorem cohnStableK2_of_conj (hC : CohnBaseChangeConjStatement)
    (hF : FieldTwoStableK2Statement) : BinaryCohnStableK2TrivialStatement :=
  cohnStableK2_of_baseChange (cohnBaseChange_of_conj hC) hF

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cohnStableK2_of_conj

/-- Stable `K₂` of the binary Leavitt algebra vanishes, given the conjugation form and
stable `K₂(𝔽₂) = 0`. -/
theorem leavittK2_of_conj (hC : CohnBaseChangeConjStatement)
    (hF : FieldTwoStableK2Statement) : BinaryLeavittStableK2TrivialStatement :=
  leavittK2_of_baseChange (cohnBaseChange_of_conj hC) hF

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2_of_conj

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
