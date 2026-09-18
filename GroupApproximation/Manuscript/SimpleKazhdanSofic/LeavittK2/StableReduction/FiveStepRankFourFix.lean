import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepRankFourFixPad
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCornerInjReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank-four fixed point versus surjective stability (sk-leavitt-36b, endpoint)

Let `L = L_{𝔽₂}(1,2)`, `σ_j = fiveStepCornerHom L j`, `pad = stab 4 L : St_4(L) → St_5(L)`, and
`D = refineHom L 1 : St_4(L) → St_5(L)`.  The lane target is lane 34c's gap
`FiveStepCornerInjRankFourFixStatement`: `σ_1` fixes `K₂(4, L)` pointwise.

## LOUD: the target is not closed here

What is proved, for any ring with a Leavitt family (`FiveStepRankFourFixConj`, `…Pad`):
`σ_r` is inner after one stabilization, `C · pad(w) · C⁻¹ = pad(σ_r w)`.  Since `pad(K₂)` is
central, `pad ∘ σ_r = pad` on `K₂(n)`.  So `σ_r` fixes `K₂(n)` exactly when `σ_r k · k⁻¹`
(in `ker pad ∩ K₂(n)`) is trivial.  This is an injective-stability question at rank four.

* **Target from injective stability at rank four** (`…_rankFourFix_of_k2StabInjective`):
  `Full.LVH2GL3.K2StabInjective L 4` gives the target.
* **The isolated statement** `FiveStepRankFourFixSurjStatement`, **surjective** stability at rank
  four: `K₂(5, L) ≤ pad(K₂(4, L))`.  It gives lane 34c's goal
  `BinaryLeavittFiveCornerInjectiveStatement` directly (`…_cornerInjective_of_surj`).  It also
  gives `BinaryLeavittK2FiveCentralStatement` (`…_central_of_surj`), and so
  `BinaryLeavittK2FiveStepStatement` (`…_fiveStep_of_surj`).
* It is **implied by the target** (`fiveStepRankFourFix_surj_of_rankFourFix`): with
  `K₂(5) = D(K₂(4))` and `D ∘ σ_1 = pad`, the equation `σ_1 v = v` gives `D v = pad v`.
* LOUD: the converse (surjective stability ⟹ target) is **not known**.  So the isolated statement
  is weaker than the target only in the sense "implied by, converse open".  It **replaces** the
  target on the way to rank-five corner injectivity.  It does **not** prove the target.
* **Truth check**: `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4; not proved in Lean) gives
  the target, hence the statement (`…_surj_of_rankFourInjective`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- **The isolated statement: surjective stability at rank four** for `L = L_{𝔽₂}(1,2)`.
Every element of `K₂(5, L)` is padded from `K₂(4, L)`.

It is implied by `FiveStepCornerInjRankFourFixStatement` (`fiveStepRankFourFix_surj_of_rankFourFix`)
and true by `K₂(4, L) = ⊥`.  LOUD: it is not known to imply `FiveStepCornerInjRankFourFixStatement`.
It suffices for `BinaryLeavittFiveCornerInjectiveStatement`. -/
def FiveStepRankFourFixSurjStatement : Prop :=
  BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
    (BooneHigman.SteinbergBasic.K2 (Fin 4) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
      (BooneHigman.SteinbergBasic.stab 4 (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FiveStepRankFourFixSurjStatement

/-- Under surjective stability, `σ_{last 4}` fixes `K₂(5, L)` pointwise: `σ_{castSucc 0}` fixes it
(`fiveStepRankFourFix_fix_of_le_map_stab`), and the fixed point moves to `last 4`. -/
theorem fiveStepRankFourFix_fixLast_of_surj (h : FiveStepRankFourFixSurjStatement) :
    ∀ w ∈ BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
      fiveStepCornerHom (BinaryLeavitt.family (ZMod 2)) (Fin.last 4) w = w :=
  fiveStepCornerInj_fix_transfer (BinaryLeavitt.family (ZMod 2)) (Fin.castSucc (0 : Fin 4))
    (Fin.last 4) (fiveStepRankFourFix_fix_of_le_map_stab (BinaryLeavitt.family (ZMod 2))
      (0 : Fin 4) h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_fixLast_of_surj

/-- **Rank-five corner injectivity from surjective stability at rank four.** -/
theorem fiveStepRankFourFix_cornerInjective_of_surj (h : FiveStepRankFourFixSurjStatement) :
    BinaryLeavittFiveCornerInjectiveStatement :=
  fiveStepCornerInj_injective_of_fix (BinaryLeavitt.family (ZMod 2)) (Fin.last 4)
    (fiveStepRankFourFix_fixLast_of_surj h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_cornerInjective_of_surj

/-- **`K₂(5, L)` is central under surjective stability**, since `pad(K₂(4))` is central. -/
theorem fiveStepRankFourFix_central_of_surj (h : FiveStepRankFourFixSurjStatement) :
    BinaryLeavittK2FiveCentralStatement := by
  intro w hw
  exact map_stab_K2_le_center (h hw)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_central_of_surj

/-- **The five-step statement `K₂(5) ↪ K₂(6)` from surjective stability at rank four.** -/
theorem fiveStepRankFourFix_fiveStep_of_surj (h : FiveStepRankFourFixSurjStatement) :
    BinaryLeavittK2FiveStepStatement :=
  binaryLeavittK2FiveStep_of_central_of_cornerInjective (fiveStepRankFourFix_central_of_surj h)
    (fiveStepRankFourFix_cornerInjective_of_surj h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_fiveStep_of_surj

/-- **The target implies surjective stability.**  Write `w ∈ K₂(5)` as `D v` with `v ∈ K₂(4)`
(`LeavittFP.K2_map_refineHom`).  Then `D v = D (σ_1 v) = pad v` (`fiveStep_refineHom_cornerHom`). -/
theorem fiveStepRankFourFix_surj_of_rankFourFix (h : FiveStepCornerInjRankFourFixStatement) :
    FiveStepRankFourFixSurjStatement := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp
    ((LeavittFP.K2_map_refineHom (BinaryLeavitt.family (ZMod 2)) (1 : Fin 4) (0 : Fin 4)
      (by decide)).ge hw)
  refine Subgroup.mem_map.mpr ⟨v, hv, ?_⟩
  have hemb : (Fin.castSuccEmb : Fin 4 ↪ Fin (4 + 1)) = Fin.castLEEmb (Nat.le_succ 4) :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  have h1 := fiveStep_refineHom_cornerHom (BinaryLeavitt.family (ZMod 2)) (1 : Fin 4) v
  rw [h v hv] at h1
  rw [h1]
  exact congrArg (fun e : Fin 4 ↪ Fin (4 + 1) =>
    indexMap (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) e v) hemb

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_surj_of_rankFourFix

/-- **Truth check**: `K₂(4, L) = ⊥` gives surjective stability at rank four. -/
theorem fiveStepRankFourFix_surj_of_rankFourInjective
    (h : LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement) :
    FiveStepRankFourFixSurjStatement :=
  fiveStepRankFourFix_surj_of_rankFourFix
    (fiveStepCornerInjRankFourFix_of_binaryLeavittSteinbergRankFourInjective h)

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_surj_of_rankFourInjective

/-- **The target from injective stability at rank four.**  If `K₂(4, L) → K₂(5, L)` is injective,
then `σ_1` fixes `K₂(4, L)` pointwise (`fiveStepRankFourFix_cornerHom_eq_of_k2StabInjective`). -/
theorem fiveStepRankFourFix_rankFourFix_of_k2StabInjective
    (h : Full.LVH2GL3.K2StabInjective (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) 4) :
    FiveStepCornerInjRankFourFixStatement := by
  intro v hv
  exact fiveStepRankFourFix_cornerHom_eq_of_k2StabInjective (BinaryLeavitt.family (ZMod 2))
    (1 : Fin 4) h hv

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepRankFourFix_rankFourFix_of_k2StabInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
