import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetTransfer
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetAction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetNatural
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetCommutative
import GroupApproximation.Manuscript.NonMFNotes.Full.CommNuclear.Unital

/-!
# Rosenberg–Schochet injectivity: the boundary maps detect zero in `Ext(S, J)`

Lane `TWWSch3d3-3D`, work order `WO-TWWSchafhauser-3d3-3D` (final assembly of
`WO-TWWSchafhauser-3d3-3`). Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through C. Schafhauser, J. reine angew. Math. 759
(2020), §5.

For a separable nuclear `S` in the UCT class and coefficients `J` with `K₁(J) = 0` and `K₀(J)`
divisible, a class `x ∈ Ext(S, J)` whose two boundary maps
`K₀(S) → K₁(J)` and `K₁(S) → K₀(J)` vanish is zero. This is the injectivity half of the
Rosenberg–Schochet universal coefficient sequence
`0 → Ext¹_ℤ(K_*S, K_{*+1}J) → Ext(S, J) → Hom(K_*S, K_{*+1}J) → 0`, whose `Ext¹_ℤ` term
vanishes for divisible `K₀(J)` and trivial `K₁(J)` (J. Rosenberg, C. Schochet, Duke Math. J. 55
(1987), Thm. 4.1; B. Blackadar, *K-theory for operator algebras*, 23.1.1).

The proof is the transfer `ExtKKAction.detectsZero_of_satisfiesUCT`: the Kasparov action of
`kasparovKK` on `Ext(-, J)` (`ExtGroup.kasparovKKAction`) preserves "both boundary maps vanish"
(`ExtGroup.kasparovKKAction_preservesNull`), commutative algebras are nuclear
(`nuclear_of_commutative`), and in the commutative case the boundary maps detect zero
(`ExtGroup.detectsZero_of_isCommutative`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

/-- **Rosenberg–Schochet injectivity** (`thm:fixed-radical-membership`, `non_mf_group_notes.tex`
l.1376--1378; Rosenberg–Schochet 1987 Thm. 4.1, Blackadar 23.1.1, Schafhauser 2020 §5).
If `S` is separable, nuclear and satisfies the UCT, `K₁(J) = 0` and `K₀(J)` is divisible,
then a class in `Ext(S, J)` whose boundary maps both vanish is zero. -/
theorem ExtGroup.eq_zero_of_boundary_eq_zero (S : SepCStarAlgebra.{0})
    (hnuc : GroupApproximation.CStarExactness.IsNuclearCStarAlgebra S)
    (hS : GroupApproximation.Full.TWWKK.kasparovKK.SatisfiesUCT S)
    (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
    [TopologicalSpace.SeparableSpace J] [Subsingleton (KOneN J)]
    (h0 : IsDivisibleGroup (KZeroN J)) (x : ExtGroup S J)
    (hx0 : ExtGroup.boundaryZero S J x = 0) (hx1 : ExtGroup.boundaryOne S J x = 0) : x = 0 :=
  ExtKKAction.detectsZero_of_satisfiesUCT (ExtGroup.kasparovKKAction J)
    (ExtGroup.kasparovKKAction_preservesNull J)
    (fun C hC => ⟨GroupApproximation.Full.CommNuclear.nuclear_of_commutative hC,
      ExtGroup.detectsZero_of_isCommutative J h0 C hC⟩)
    hnuc hS x ⟨hx0, hx1⟩

end GroupApproximation.Full.TWWSchafhauser
