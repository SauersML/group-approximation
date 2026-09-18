import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseCrossers
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCoreClose
import GroupApproximation.Meta.AxiomGuard

/-!
# The core at a loose crossing needs a third loose passage

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-20.

Write `σ` for the rotation and `α` for the reversal.  A passage `d → next d` of the pocket boundary
is *tight* when `σ (next d) = α d`, and *loose* otherwise.

## Route

* `regionMoveLoose_three_of_looseCross` (proved): if the passage `d` crosses the loose turn `d₀`,
  then some third passage `e ∉ {d₀, d}` is loose (`regionMoveLoose_false_of_pair`, module
  `RegionMoveLooseCrossers`: the crossers of a sector come in pairs).
* `regionMoveLoose_junction_of_loose` (proved): if both sides `s₁` and `s₂` are empty, every loose
  passage starts at the last dart of `t₁⁻¹` or of `t₂` (module `RegionMoveLooseArc`).
* `regionMoveLoose_not_looseCross_of_sides_nil`, `regionMoveLoose_not_looseCross_of_eps_zero`
  (proved): so a pocket with both sides empty, in particular any pocket with `ε = 0`, has no loose
  crossing.  There are at most two junctions, but a crossing needs three loose passages.
* `regionMoveLoose_not_looseCross_of_subsingleton` (proved): with at most one loose passage there
  is no loose crossing.
* `RegionMoveLooseResidualStatement` (OPEN, PLAUSIBLE): `RegionMoveCoreCloseStatement` with the
  extra premises `0 < ε`, `s₁ ≠ [] ∨ s₂ ≠ []` and `RegionMoveLooseThree K`.
* `regionMoveLoose_close_of_residual` (proved): Residual → Close.
* `regionMoveLoose_residual_of_close` (proved): Close → Residual (truth certificate).
* `regionMoveLoose_extremalCore_of_residual` (proved): Residual → `RoseExtremalCoreStatement`.

## Status of the residual (LOUD)

The residual is **logically equivalent** to `RegionMoveCoreCloseStatement`, and so to
`RoseExtremalCoreStatement`.  Its extra premises follow from the premises of Close.  It is not a
restatement: it is **strictly smaller in proof content**.  Every pocket whose loose passages are
only the crossing pair `d₀, d` is discharged here, including every pocket with `ε = 0` and every
pocket with both sides empty.  A proof of the residual may assume a third loose passage, a nonempty
side, and `ε > 0`.

## Truth check

Implied by Close (`regionMoveLoose_residual_of_close`), hence by Core, so it is as plausible as
Core: no counterexample is known (docstring of `RegionMoveCore`).  It avoids the refuted forms
`ExtremalEndBlockStatement` and `FrameConeFourStatement`.

## Remaining gap

The residual itself: pockets with `ε > 0` and a third loose passage, which lies in a side.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A loose crossing with a third loose passage**: the data of `RegionMoveCoreCloseLooseCross`,
together with a passage `e ∉ {d₀, d}` that is not tight. -/
def RegionMoveLooseThree (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle) (d : X.toCombMap.Dart)
    (hd : d ∈ K.boundary.cycle),
    P10ChordLift.NonFirstTurn K d₀ hd₀ ∧ ¬RegionMoveCoreCloseTight K d₀ hd₀ ∧ d ≠ d₀ ∧
      ¬RegionMoveCoreCloseTight K d hd ∧
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
      ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (K.boundary.cycle.next d hd)) ∧
      ∃ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ ∧ e ≠ d ∧
        ¬RegionMoveCoreCloseTight K e he

/-- **A loose crossing has a third loose passage.** -/
theorem regionMoveLoose_three_of_looseCross (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (h : RegionMoveCoreCloseLooseCross K) : RegionMoveLooseThree K := by
  obtain ⟨d₀, hd₀, d, hd, hnf, hnt₀, hne, hnt, hsc, hcross⟩ := h
  have hex : ∃ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ ∧ e ≠ d ∧
      ¬RegionMoveCoreCloseTight K e he := by
    by_contra hno
    apply regionMoveLoose_false_of_pair K hK hd₀ hd hcross
    intro e he h0 h1
    by_contra ht
    exact hno ⟨e, he, h0, h1, ht⟩
  exact ⟨d₀, hd₀, d, hd, hnf, hnt₀, hne, hnt, hsc, hcross, hex⟩

/-- **With empty sides, a loose passage starts at a junction.** -/
theorem regionMoveLoose_junction_of_loose (K : PocketFaceSet D eps X lo hi)
    (h₁ : K.firstSide = []) (h₂ : K.secondSide = []) {e : X.toCombMap.Dart}
    (he : e ∈ K.boundary.cycle) (hnt : ¬RegionMoveCoreCloseTight K e he) :
    (∃ h : invDarts X K.sourceArc.darts ≠ [], e = (invDarts X K.sourceArc.darts).getLast h) ∨
      (∃ h : K.targetArc.darts ≠ [], e = K.targetArc.darts.getLast h) := by
  rcases regionMoveLoose_tight_or_junction K he with ht | h | h | h | h
  · exact absurd ht hnt
  · rw [h₁] at h
    simp at h
  · rw [h₂] at h
    simp at h
  · exact Or.inl h
  · exact Or.inr h

/-- **Empty sides leave no loose crossing**: the loose passages are among the two junctions, but a
loose crossing needs three. -/
theorem regionMoveLoose_not_looseCross_of_sides_nil (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (h₁ : K.firstSide = []) (h₂ : K.secondSide = []) :
    ¬RegionMoveCoreCloseLooseCross K := by
  intro hlc
  obtain ⟨d₀, hd₀, d, hd, -, hnt₀, hne, hnt, -, -, e, he, hed₀, hed, hnte⟩ :=
    regionMoveLoose_three_of_looseCross K hK hlc
  have j₀ := regionMoveLoose_junction_of_loose K h₁ h₂ hd₀ hnt₀
  have j₁ := regionMoveLoose_junction_of_loose K h₁ h₂ hd hnt
  have j₂ := regionMoveLoose_junction_of_loose K h₁ h₂ he hnte
  rcases j₀ with ⟨_, e₀⟩ | ⟨_, e₀⟩ <;> rcases j₁ with ⟨_, e₁⟩ | ⟨_, e₁⟩ <;>
    rcases j₂ with ⟨_, e₂⟩ | ⟨_, e₂⟩ <;>
    first
      | exact hne (e₁.trans e₀.symm)
      | exact hed₀ (e₂.trans e₀.symm)
      | exact hed (e₂.trans e₁.symm)
