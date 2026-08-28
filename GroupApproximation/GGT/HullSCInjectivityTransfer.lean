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
builds the rotating family rather than on the side that cites DGO.  This module
is the one lemma that discharge needs, in the form it will be consumed:

> if every nontrivial element of the kernel moves the basepoint by at least `L`,
> and `L` exceeds `2R`, then the quotient map is injective on the `R`-ball of
> `Γ(G,A)`.

`injOn_cayleyBall_of_action` does the geometry -- a word of length at most `2R`
in letters that move the basepoint by at most one moves it by at most `2R` --
and this lemma supplies its hypothesis from the kernel.

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

/-- **Injectivity on a ball of `Γ(G,A)`, from the kernel moving the
basepoint.**

The space is arbitrary: the only comparison with `Γ(G,A)` is that the letters of
`A` move the basepoint by at most one, which is what
`injOn_cayleyBall_of_action` turns into `d(y, g·y) ≤ |g|_A`.  So this applies
verbatim on the geodesic realisation `Point A`, where the rotating family
actually lives, and the transfer back to `Γ(G,A)` costs nothing because the
vertex inclusion has distortion one. -/
theorem injOn_cayleyBall_of_kernel_moves {G : Type u} [Group G] {Q : Type*}
    [Group Q] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) (A : Alphabet G) (y : X)
    (hA : ∀ a ∈ A.carrier, dist y (a • y) ≤ 1) (q : G →* Q) {K : Subgroup G}
    (hker : q.ker = K) {L : ℝ} (R : ℕ) (hL : 2 * (R : ℝ) < L)
    (hmove : ∀ g ∈ K, g ≠ 1 → L ≤ dist y (g • y)) :
    Set.InjOn q (cayleyBall A R) := by
  refine injOn_cayleyBall_of_action hiso A y hA q (L := L) R hL ?_
  intro g hg hdist hq
  have hmem : g ∈ K := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hq
  have hge : L ≤ dist y (g • y) := hmove g hmem hg
  linarith

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
