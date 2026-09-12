import GroupApproximation.GGT.DGOProposition414GapComponentAssembly

/-!
# Complete target/isolation families for balanced gap children

The component-configuration residue in Proposition 4.14 is exactly the
target-component and isolation assertion on each of the four canonical gap
cycles.  This module names that residue independently of the finite
enumeration (`all`, labels, positions, exhaustion, and separation) used by
`AuxiliaryCycleComponentConfiguration`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The complete four-family target/isolation output for the two gap halves.
This is strictly smaller than `GapComponentConfigurations`: it retains only
the geometric component and isolation assertions, leaving finite start
enumeration and its exhaustion/separation bookkeeping to the landed
constructor. -/
structure CompleteTargetIsolationFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  firstTarget : ∀ j, ∀ s ∈ B.firstGapTarget j,
    IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
      (B.firstGapCut j s) (B.firstGapCut j (s + 1))
  firstIsolated : ∀ j, ∀ s ∈ B.firstGapTarget j,
    IsIsolated D.fam (B.firstGapLocalLabel j s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j))
      (B.firstGapCycle j) (B.firstGapCut j s)
  secondTarget : ∀ j, ∀ s ∈ B.secondGapTarget j,
    IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
      (B.secondGapCut j s) (B.secondGapCut j (s + 1))
  secondIsolated : ∀ j, ∀ s ∈ B.secondGapTarget j,
    IsIsolated D.fam (B.secondGapLocalLabel j s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j))
      (B.secondGapCycle j) (B.secondGapCut j s)

/-- The complete target/isolation family produces the full pair of canonical
gap component configurations. -/
noncomputable def CompleteTargetIsolationFamily.toConfigurations
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : CompleteTargetIsolationFamily B) :
    GapComponentConfigurations hsymm hδ P B :=
  B.gapComponentConfigurations_of_targetIsolated
    F.firstTarget F.firstIsolated F.secondTarget F.secondIsolated

/-- Existential packaging for consumers of the component-configuration
producer. -/
theorem exists_gapComponentConfigurations_of_completeTargetIsolation
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : CompleteTargetIsolationFamily B) :
    Nonempty (GapComponentConfigurations hsymm hδ P B) :=
  ⟨F.toConfigurations⟩

/-- Empty target sets give a concrete vacuous model of the complete-family
interface.  This tests all four dependent fields without assuming any
unproved geometric assertion. -/
theorem CompleteTargetIsolationFamily.emptyTargetModel
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hfirst : ∀ j, B.firstGapTarget j = ∅)
    (hsecond : ∀ j, B.secondGapTarget j = ∅) :
    Nonempty (CompleteTargetIsolationFamily B) := by
  refine ⟨
    { firstTarget := ?_
      firstIsolated := ?_
      secondTarget := ?_
      secondIsolated := ?_ }⟩
  · intro j s hs
    simp [hfirst j] at hs
  · intro j s hs
    simp [hfirst j] at hs
  · intro j s hs
    simp [hsecond j] at hs
  · intro j s hs
    simp [hsecond j] at hs

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
