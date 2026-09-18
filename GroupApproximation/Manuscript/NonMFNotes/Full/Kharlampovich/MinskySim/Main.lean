import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.StepSim
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.Transport

/-!
# Minsky machines simulate modular machines

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  For every
modular machine there is a deterministic Minsky machine with five glasses and a
start state such that, from `α`, `β` in the first two glasses, the machine
reaches the stop configuration exactly when `(α, β)` halts.  We combine the
simulation `MinskySim.simulates` with the transport
`MinskySim.TMachine.exists_minsky_of_tmachine`.
-/

namespace GroupApproximation.Full.Kharlampovich

/-- Every modular machine is simulated by a deterministic Minsky machine
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem exists_minsky_simulating (mm : BooneGroup.ModularMachine) :
    ∃ (K N : ℕ) (M : Minsky.Machine K N) (s : Fin (N + 1)), M.Deterministic ∧
      ∀ p : ℕ × ℕ,
        M.Reaches ⟨s, Minsky.initGlasses K p.1 p.2⟩ (Minsky.stopCfg K N) ↔ mm.Halts p := by
  obtain ⟨N, M, s, hdet, hM⟩ :=
    (MinskySim.tm mm).exists_minsky_of_tmachine (MinskySim.St.divA (MinskySim.ix mm 0))
  exact ⟨5, N, M, s, hdet, fun p ↦
    (hM (Minsky.initGlasses 5 p.1 p.2)).trans ((MinskySim.simulates mm).halts_iff p).symm⟩

end GroupApproximation.Full.Kharlampovich
