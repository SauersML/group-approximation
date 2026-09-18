import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinSelfBound
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell-bound region choice with the all-pairs shared-arc bound supplied

Lane gl-p10-81.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The two statements

* `roseLobeOsinSelf_Statement` is `roseLobeOsinCore_Statement` with the premise
  `roseLobeOsinSelf_SharedArcBoundAll X μ` (module `OsinSelfBound`) inserted right after
  `X.LeastArea`.  This covers arcs a cell shares with itself as well.
* `roseLobeOsinSelf_NonGenStatement` is the residual of the self case.  It has the threshold
  shape of the core statement, `∃ ε₀, ∀ ε ≥ ε₀, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀`, and then, for every
  diagram `X` with the cell bounds, least area and letter labels, it gives
  `roseLobeOsinSelf_NonGenericBound X μ`.

## The reductions

* `roseLobeOsinSelf_core_of`: the two statements give the core statement.  Take
  `ε₀ = max ε₀' ε₀''` and then `ρ₀ = max ρ₀' ρ₀''`.  The all-pairs premise is supplied by
  `roseLobeOsinSelf_sharedArcBound`.
* `roseLobeOsinSelf_of_core`: the core statement gives `roseLobeOsinSelf_Statement`, by dropping
  the premise.
* `roseLobeOsinSelf_of_piece`: `roseLobeOsinPiece_Statement` gives it too, since the all-pairs
  bound implies the distinct-pairs one (`roseLobeOsinSelf_pairs_of_all`).

## Strength (LOUD)

* `roseLobeOsinSelf_Statement` is implied by both the core statement and the piece statement.
  It is equivalent to them only modulo the residual `roseLobeOsinSelf_NonGenStatement`.  It is
  **not** proved equivalent here.
* The residual is strictly smaller in proof content than the core statement.  It is a local
  statement about one relator cell of one diagram.  It has no pocket, no region choice and no
  planar pocket hypotheses.  It is needed only in the non-generic, self-shared case.
* **Truth of the residual** (OPEN, not refuted; scratchpad `gl-p10-81/self_arc.py`).
  1. Planarity.  In all 18596 connected planar maps with at most 4 edges, every edge whose two
     darts lie on one face is a bridge (28193 cases).  Every edge of every self-overlap arc is
     such an edge (108092 arcs).  So the cell reads cyclically `w X w⁻¹ Y`, and `X` bounds a
     sub-diagram `C₂` that holds no outer face.
  2. Free groups.  Here non-genericity forces the relator value to be `1` (no counterexample
     among 161² pairs of reduced words).  That is excluded by qg and long.
  3. Torsion.  In `D∞` non-genericity occurs with a relator value of infinite order.  So the
     residual is NOT a formal consequence of the genericity algebra.  Its expected proof is
     qg when `C₂` has no relator cell, and otherwise Greendlinger's lemma on the least-area
     sub-diagram `C₂` whose boundary is a qg arc of the cell.  That is an area induction
     inside the main theorem.
  4. The earlier long/qg/pieces audit (`OsinCoreStatement`, 1260 configurations) was not
     rerun with the self-overlap premise.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The non-generic self-overlap residual** (OPEN, not refuted; see the module docstring).
Beyond thresholds `ε₀`, `ρ₀`, every diagram with the cell bounds, least area and letter labels
has the non-generic self-overlap bound. -/
def roseLobeOsinSelf_NonGenStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W),
            roseLobeOsinCore_CellBounds D W X eps mu lambda c rho → X.LeastArea →
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                roseLobeOsinSelf_NonGenericBound X mu

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_NonGenStatement
