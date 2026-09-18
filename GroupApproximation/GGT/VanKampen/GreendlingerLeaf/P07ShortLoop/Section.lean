import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# P07 short loop: the all-cells residual in section form

## WARNING: `AllCellsShortLoopStatement` is believed FALSE as stated

`P07LakeExclusion.AllCellsShortLoopStatement` (`P07LakeExclusion/Proof.lean:202`) quantifies over
every `D`, `ε`, `ρ` satisfying `OsinCCondition` plus `2 ≤ ρ` and the width budget.  It has **no
hyperbolicity hypothesis**, and its thresholds are effectively `ε₀ = 0` and a `ρ₀` that does not
depend on `δ`.  A counterexample needs only **one** relator cell: then `OsinLemma97Below … 1` is
vacuous, and the diagram is least-area as soon as its boundary value is not `1`.  Take a relator
`R`, cyclically `(λ, c)`-quasi-geodesic, with small `ε`-pieces, of length above
`32 (3ε + c) / λ`, whose value is conjugate by a long `h` to an element of norm `≤ 2ε`.  Let `X`
be the `R`-cell, a spur labelled `h`, and a `G`-face bounded by the short loop.  Then the enclosed
set `{R-cell, G-face}` has outer walk of length `≤ 2ε`, which gives the forbidden `s₁ ++ s₂`.

Candidate data: `G = F₂ × F₂` (word norm = sum of reduced lengths), with `R` interleaving
the tents `w b w⁻¹` and `w' y w'⁻¹` (aperiodic `w`, `w'` at a quarter-period phase offset), so that
`λ ≈ 1/2`, `c` is small, and the value is conjugate by `(w, w')` to `(b, y)` of norm `2`.

**No Lean refutation is given.**  It needs words of several hundred letters, and checking
`IsLambdaCQuasiGeodesicWord` and the piece bound for them by kernel evaluation alone is out of
reach.  The obstruction is exactly the missing hyperbolicity: in a `δ`-hyperbolic `G`,
quasi-geodesic long relators cannot be conjugate to short elements by a spur that fits.

## The strictly weaker residual

`p07ShortLoop_SectionStatement` keeps every hypothesis of `AllCellsShortLoopStatement`.  It adds
the target's hyperbolicity of `D.alphabet.carrier`, and it lets `ε₀` depend on `(D, λ, c, μ)` and
`ρ₀` depend on `ε`.  This is the thresholded form in which the target
`CellPocketWalkProperArcsBelowSectionStatement` is stated.  `p07ShortLoop_section_of_allCells`
shows it is implied by the old residual (take `ε₀ = ρ₀ = 0`), so it is weaker.
`p07ShortLoop_proof_of_section` shows it still yields the target.  Mathematically it is
Greendlinger's lemma at the current induction level for the least-area enclosed subdiagram with a
short boundary.  That is true (Osin, Lemma 9.7) once `ε`, `ρ` exceed the `δ`-dependent constants.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07ShortLoop

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides
open GreendlingerLeaf.P07LakeExclusion

/-- **The all-cells short-loop residual, beyond hyperbolic thresholds.**  The body is that of
`AllCellsShortLoopStatement`.  It is guarded by the hyperbolicity of `D.alphabet.carrier` and by
thresholds `ε₀`, `ρ₀` chosen after `(D, λ, c, μ)` and `ε`. -/
def p07ShortLoop_SectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho → 2 ≤ rho →
            lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) →
            ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea →
              OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
              OEquivalentDiscDiagram Delta X →
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
              ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
                EnclosedFaceSetSucc X faces outerWalk →
                (∃ C ∈ X.relatorCells, C.face ∈ faces) →
                (∀ k : Fin X.rCellCount, (cell X k).face ∈ faces) →
                ∀ s₁ s₂ : List X.toCombMap.Dart, invDarts X outerWalk = s₁ ++ s₂ →
                  s₁.length ≤ eps → s₂.length ≤ eps → False

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07ShortLoop.p07ShortLoop_SectionStatement

/-- **Weakening.**  The unthresholded residual implies the section form at `ε₀ = ρ₀ = 0`, and it
ignores the hyperbolicity witness. -/
theorem p07ShortLoop_section_of_allCells (h : AllCellsShortLoopStatement.{u, w, v}) :
    p07ShortLoop_SectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ⟨0, fun rho _ W hcondition hrho hlarge => ?_⟩⟩
  exact h D eps rho mu lambda c hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07ShortLoop.p07ShortLoop_section_of_allCells

/-- **The Piece 07 `Below` section from the section-form residual.**  This follows
`P07LakeExclusion.proof_of_gaps`.  Step 1 is `LakeFill.lakeFillSucc` and step 2 is
`false_of_enclosedSucc`.  Step 3 is the hypothesis at `ε₀` from `hsec` and
`ρ₀ = max 2 (max ρ₁ ρ_S)`, and the hyperbolicity witness is passed through. -/
theorem p07ShortLoop_proof_of_section (hsec : p07ShortLoop_SectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps0, heps0⟩ := hsec D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rhoS, hrhoS⟩ := heps0 eps heps
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 (max rho1 rhoS), by omega, fun rho hrho W hcondition => ?_⟩
  have hrho2 : 2 ≤ rho := by omega
  have hrho1' : rho1 ≤ rho := by omega
  have hrhoS' : rhoS ≤ rho := by omega
  have hlarge := hrho1 rho hrho1'
  have hshort := hrhoS rho hrhoS' W hcondition hrho2 hlarge
  intro Delta _ hlea hbelow S i j _ _ _ _ _ hij _ _ _ K _ _ _ _ hw hoff
  have hfalse : K.firstArc.length = (cellDarts S.diagram i).length ∨
      K.secondArc.length = (cellDarts S.diagram j).length → False := by
    intro hfull
    obtain ⟨faces, outerWalk, s₁, s₂, E, ⟨C, hC, hCf⟩, hs₁, hs₂, hcases⟩ :=
      LakeFill.lakeFillSucc D eps S.diagram K hij hw hoff hfull
    rcases hcases with ⟨k, A, hk, hdec⟩ | ⟨hall, hdec⟩
    · exact false_of_enclosedSucc hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge hlea
        hbelow S.equiv S.label_admissible E hC hCf hk A hdec hs₁ hs₂
    · exact hshort Delta S.diagram hlea hbelow S.equiv S.label_admissible faces outerWalk E
        ⟨C, hC, hCf⟩ hall s₁ s₂ hdec hs₁ hs₂
  exact ⟨lt_of_le_of_ne K.firstArc.length_le fun h => hfalse (Or.inl h),
    lt_of_le_of_ne K.secondArc.length_le fun h => hfalse (Or.inr h)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07ShortLoop.p07ShortLoop_proof_of_section

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07ShortLoop
