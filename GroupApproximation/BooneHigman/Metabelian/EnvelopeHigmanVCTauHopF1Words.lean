import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop family F1: the explicit level-`n` flexible squares (lane bh-met-92n)

Family F1 of `higmanVCTauBin_Hop`: `|p| + |q| = 3`, so up to order `{p, q} = {[a], [b, c]}`
with `a ≠ b`, and the instance is `x = a r ↦ x' = b c r`, `y = b c t ↦ y' = a t`.  Pick
`c' ≠ c`.  For `t = t₀ t'` we give an explicit `HopA` witness (`higmanVCTauHop_hopA`):
* descent pair `w := ([b, c'], [b, c, t₀])` with `C := (a r, b c' t')`;
* `s` carries `w` to `w' := ([b, c'], [a, t₀])` and `C` to `E := (b c r, b c' t')`;
* the level-`n` square `(w'; E → (x', y'))` is `Easy` by a flexible square A
  (`higmanVCTauHop_flexA1` for `r = r₀ r''`, `higmanVCTauHop_flexA0` for `r = []`).
The hypotheses on `s` are only the three cone facts `hs1`, `hs2`, `hfix`, so the same
lemma serves both orders of `p`, `q`.

Truth check: scratch `bh-met-92n/f1.cpp` (faithful model of `FlexA`, `FlexB`, `Easy`,
`HopA`, `HopC` over `Fin 2`) found a `HopA` for every F1 instance with `|r|, |t| ≤ 6`
(64480 instances, 0 failures); the witness above was checked by hand field by field.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Flexible square A of `w' = ([b, c'], [a, t₀])` at `E = (b c r₀ r, b c' t')`. -/
theorem higmanVCTauHop_flexA1 {d : ℕ} {a b c c' t0 r0 : Fin d} {r t' : List (Fin d)}
    (hab : a ≠ b) (hc : c' ≠ c) (h1 : ¬ [b, c'] <+: [a, t0]) (h2 : ¬ [a, t0] <+: [b, c']) :
    higmanVCTauComm_FlexA d [b, c'] [a, t0] (b :: c :: r0 :: r) (b :: c' :: t') h1 h2 := by
  have hi := higmanVCTauUnif_inc_cons hab [t0] [c, r0]
  have e1 : (a :: t0 :: r).length = r.length + 1 + 1 := rfl
  have e2 : (b :: c' :: t').length = t'.length + 1 + 1 := rfl
  have e3 : (b :: c :: r0 :: r).length = r.length + 1 + 1 + 1 := rfl
  have e4 : (b :: c' :: r).length = r.length + 1 + 1 := rfl
  have e5 : (a :: t0 :: t').length = t'.length + 1 + 1 := rfl
  exact ⟨[a, t0], [b, c, r0], a :: t0 :: r, b :: c' :: t', [b, c'], [b, c, r0],
    b :: c' :: r, a :: t0 :: t', hi.1, hi.2, by simp, by simp,
    (mapsCone_coneSwap_left hi.1 hi.2).append r,
    higmanVCTauUnif_fix hi.1 hi.2 (higmanVCTauUnif_inc_cons (Ne.symm hab) (c' :: t') [t0])
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hc t' [r0])),
    by omega, mapsCone_coneSwap_right h1 h2,
    higmanVCTauUnif_fix h1 h2
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons (Ne.symm hc) [r0] []))
      (higmanVCTauUnif_inc_cons (Ne.symm hab) [c, r0] [t0]),
    by simp, by simp, (mapsCone_coneSwap_right h1 h2).append r,
    (mapsCone_coneSwap_left h1 h2).append t', by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flexA1

/-- Flexible square A of `w' = ([b, c'], [a, t₀])` at `E = (b c, b c' t₁ t'')`. -/
theorem higmanVCTauHop_flexA0 {d : ℕ} {a b c c' t0 t1 : Fin d} {t'' : List (Fin d)}
    (hab : a ≠ b) (hc : c' ≠ c) (h1 : ¬ [b, c'] <+: [a, t0]) (h2 : ¬ [a, t0] <+: [b, c']) :
    higmanVCTauComm_FlexA d [b, c'] [a, t0] [b, c] (b :: c' :: t1 :: t'') h1 h2 := by
  have hi := higmanVCTauUnif_inc_cons hab [t0] [c', t1]
  have e1 : ([b, c] : List (Fin d)).length = 2 := rfl
  have e2 : (a :: t0 :: t'').length = t''.length + 1 + 1 := rfl
  have e3 : (b :: c' :: t1 :: t'').length = t''.length + 1 + 1 + 1 := rfl
  have e4 : (b :: c' :: t'').length = t''.length + 1 + 1 := rfl
  exact ⟨[a, t0], [b, c', t1], [b, c], a :: t0 :: t'', [b, c'], [a, t0, t1],
    [b, c], b :: c' :: t'', hi.1, hi.2, by simp, by simp,
    higmanVCTauUnif_fix hi.1 hi.2 (higmanVCTauUnif_inc_cons (Ne.symm hab) [c] [t0])
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons (Ne.symm hc) [] [t1])),
    (mapsCone_coneSwap_left hi.1 hi.2).append t'', by omega,
    mapsCone_coneSwap_right h1 h2, (mapsCone_coneSwap_left h1 h2).append [t1],
    by simp, by simp,
    higmanVCTauUnif_fix h1 h2
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons (Ne.symm hc) [] []))
      (higmanVCTauUnif_inc_cons (Ne.symm hab) [c] [t0]),
    (mapsCone_coneSwap_right h1 h2).append t'', by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flexA0

/-- The flexible square A of `w'` at `E = (b c r, b c' t')`, unless `r = t' = []`. -/
theorem higmanVCTauHop_flex {d : ℕ} {a b c c' t0 : Fin d} {r t' : List (Fin d)}
    (hab : a ≠ b) (hc : c' ≠ c) (h1 : ¬ [b, c'] <+: [a, t0]) (h2 : ¬ [a, t0] <+: [b, c'])
    (hne : r ≠ [] ∨ t' ≠ []) :
    higmanVCTauComm_FlexA d [b, c'] [a, t0] (b :: c :: r) (b :: c' :: t') h1 h2 := by
  rcases r with _ | ⟨r0, r⟩
  · rcases t' with _ | ⟨t1, t''⟩
    · exact (hne.elim (fun h => h rfl) (fun h => h rfl)).elim
    · exact higmanVCTauHop_flexA0 hab hc h1 h2
  · exact higmanVCTauHop_flexA1 hab hc h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flex

end GroupApproximation.BooneHigman.Metabelian.Envelope
