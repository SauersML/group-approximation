import GroupApproximation.GGT.HullSCFilling

/-!
# Injectivity on a ball from the kernel moving the basepoint

The injectivity radius of Hull's Theorem 5.1 is **not** a conclusion of
Dahmani-Guirardel-Osin's Theorem 5.3.  Read from the source, 5.3 concludes two
things: the free splitting `⟨⟨H⟩⟩^G = ∗_{t∈T} t⁻¹Ht`, and that every element of
`⟨⟨H⟩⟩^G` is conjugate into `H` or is loxodromic.  Neither is metric at the
scale the injectivity clause needs -- loxodromy is asymptotic and gives nothing
at a single translate, and the splitting is not metric at all.  The nearest
metric statement in the paper, Theorem 2.17(b), is that the quotient of the
*space* is a local isometry away from the apices, which is a different
statement from a bound on the kernel of the quotient of the *group*.

So the injectivity radius is Hull's own §5, and it belongs on the side that
builds the rotating family rather than on the side that cites DGO.  The lemma
discharge needs is

> if every nontrivial element of the kernel moves the basepoint by at least `L`,
> and `L` exceeds `2R`, then the quotient map is injective on the `R`-ball of
> `Γ(G,A)`,

which is `HullSC.injOn_cayleyBall_of_kernel_moves`, stated in
`GGT/HullSCFilling.lean` beside `injOn_cayleyBall_of_action` -- the geometry
that a word of length at most `2R` in letters moving the basepoint by at most
one moves it by at most `2R` -- because Hull's Theorem 5.1 consumes it there.
What this module adds is the form the family hands back, with the kernel
presented as the normal closure of the rotations, and the reading below of why
the hypothesis is the right one.

## The non-vacuity check it encodes

`hmove` is the check in positive form, and it is not a formality: a quotient
faithful below `L` at the basepoint forces every nontrivial element of the
kernel to move the basepoint at all, so a family one of whose rotations fixes
the chosen basepoint admits no such quotient, whatever the space.  That is the
shape of the refutation of the ungeodesic `HullSC.DGOQuotientStatement` --- a
trivial action on a space whose distances miss the annulus --- and the repaired
`HullSC.DGOQuotientStatementGeodesic` keeps the basepoint `ρ`-far from every
apex for the same reason.  So placing the family on a space is not finished
until the basepoint is checked against the kernel, and `hmove` states that check
once, where it cannot be skipped.

Quantifying over the kernel rather than over all of `G` is what makes it true:
an element outside the kernel may fix the basepoint without harm, and in a
Cayley graph of `G` no element fixes anything, which is the other half of why
the family cannot live there (`HullSC.rot_eq_bot_of_cayley`).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- The same, with the kernel given as the subgroup the rotations of a family
generate -- the form `HullSC.RotatingQuotient.ker_eq` hands back. -/
theorem injOn_cayleyBall_of_rotations_move {G : Type u} [Group G] {Q : Type*}
    [Group Q] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) (A : Alphabet G) (y : X)
    (hA : ∀ a ∈ A.carrier, dist y (a • y) ≤ 1) (q : G →* Q) {C : Set X}
    {Rot : X → Subgroup G} (hker : q.ker = rotationNormalClosure C Rot) {L : ℝ}
    (R : ℕ) (hL : 2 * (R : ℝ) < L)
    (hmove : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 → L ≤ dist y (g • y)) :
    Set.InjOn q (cayleyBall A R) :=
  injOn_cayleyBall_of_kernel_moves hiso A y hA q hker R hL hmove

end HullSC
end GroupApproximation
