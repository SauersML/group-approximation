---
title: STW Problem LXXXVI --- the Berend frontier of Eckhardt--Wu Conjecture II (2026-08-30)
---

Problem LXXXVI (Eckhardt--Wu, arXiv:2408.07223, Conjecture II): a finitely
generated elementary amenable group is virtually nilpotent iff `C*(G)` has
finite decomposition rank.

## Status screen (2026-08-30)

Backward direction: virtually nilpotent ⟹ finite decomposition rank
(Eckhardt--Gillaspy--McKenney, arXiv:1706.04142).  Forward direction open.
Known: for `G = Z^d ⋊ Z`, finite decomposition rank implies strong
quasidiagonality by Kirchberg--Winter, Theorem 5.3, and strong
quasidiagonality in turn forces virtual nilpotence by Eckhardt,
Theorem 3.3.  The converse implication "strongly quasidiagonal implies
finite decomposition rank" is not being used.  Eckhardt--Wu 2024 verify
the conjecture for wreath products `K ≀ H` of virtually nilpotent groups
(their Theorem D) and observe `C*(H_3(Z[1/p]) ⋊ Z)`-type groups are not
strongly QD.

## The frontier

Eckhardt's Theorem 2.4 (arXiv:1309.2205): for the action of a rank-two
subgroup of the unit group of a totally real cubic field on its ring of
integers `Z^3`, the group `G = Z^3 ⋊ Z^2` is polycyclic, exponential
growth, NOT virtually nilpotent, and `C*(G)` IS strongly quasidiagonal —
by Berend's orbit dichotomy on `T^3` (every orbit finite or dense) and the
Archbold--Spielberg topological-freeness argument.

For these groups the two most immediate obstructions are silent: all
representations are quasidiagonal, and nuclear dimension is finite by
Eckhardt--Wu, Theorem 5.4.  Eckhardt's proof also shows that every proper
quotient is subhomogeneous, but it does not identify every quotient with a
single `M_{|O|}(C(T^2))`.  The numerical bound `53` in Eckhardt--Wu belongs
to a different example, not this one.  Decomposition rank is not known to
be monotone under the non-strongly-QD subgroups `Z^3 ⋊ Z`.  So Conjecture
II's forward direction, restricted to this concrete unresolved instance,
asserts `dr(C*(Z^3 ⋊ Z^2)) = ∞`; the methods recorded above do not
decide it.

## Candidate mechanism: entropy against decomposition rank

Every nonidentity element of the chosen torsion-free unit subgroup acts on
`T^3` with positive topological entropy: an infinite-order algebraic unit
cannot have all conjugates of modulus one.  A new theorem saying, for this
class of algebraic actions, that finite decomposition rank forces zero
entropy of each acting automorphism would settle the Berend case, but the
general version of that implication is rigorously false.  Indeed
`minimal-cantor-crossed-products-have-decomposition-rank-one` proves that
every Cantor minimal `Z`-crossed product has decomposition rank one, and
strictly ergodic examples of positive entropy exist.  Any viable entropy
obstruction must therefore use the higher-rank algebraic action or the
nonminimal finite-orbit structure.  The finite invariant torsion sets
underlying quasidiagonality do not currently yield the contractive
order-zero approximations required for decomposition rank.  The open node is
`stw99-lxxxvi-berend-groups-decomposition-rank`.

## Exact quotient reduction

`berend-proper-quotients-have-decomposition-rank-at-most-two` strengthens
the nonfaithful-representation half of Eckhardt's argument.  Every proper
quotient factors through the crossed product over a finite invariant set.
Orbit by orbit this is `M_{|O|}(C(T^2))`, because a finite-orbit stabilizer
has finite index in `Z^2`.  Consequently every proper quotient has
decomposition rank at most two.  The desired infinite decomposition rank,
if true, is therefore invisible in all proper quotients.

The quotient family is nevertheless norm-complete.  By residual finite
dimensionality, enumerate the finite orbits and take their increasing
finite unions `F_n`.  The quotient maps
`C(T^3) ⋊ Z^2 -> C(F_n) ⋊ Z^2` are asymptotically isometric, so they
embed the full crossed product into the quotient of the product of these
decomposition-rank-two targets by their direct sum.  This does not bound
the source decomposition rank: restrictions of `C(Y)` to increasing dense
finite subsets are asymptotically isometric with finite-dimensional
targets for every compact metrizable `Y`, while `dr(C(Y)) = dim(Y)` can be
arbitrary.  The remaining positive hinge is therefore an internal
order-zero-compatible lifting theorem, not stronger finite-orbit norm
separation.

The primitive spectrum makes the same boundary visible topologically.
The zero ideal is primitive and is the unique dense point.  Every nonzero
primitive ideal is maximal with finite-dimensional quotient; setwise the
remainder is a countable union of closed two-tori, one dual stabilizer for
each finite orbit.  Therefore neither an individual primitive quotient nor
the dimension of a closed primitive stratum can force infinite
decomposition rank.  A primitive-space proof would have to quantify the
global accumulation of these strata at the faithful generic point.

This limitation is exact.  Every closed primitive subset omitting `0` is
the spectrum of a proper quotient, hence a finite union of closed subsets
of orbit two-tori.  Every nonempty open primitive subset contains `0`.
It follows that every locally closed Hausdorff primitive subspace has
covering dimension at most two, with equality on each full orbit torus.
Thus ordinary primitive-space dimension is exactly two.  Moreover every
nonzero ideal retains the generic point, while a proper quotient isolates
only finitely many closed orbit strata.  No ideal filtration using only
the finite-orbit type-I layers eliminates the faithful accumulation core.

## Sources

* C. Eckhardt, A note on strongly quasidiagonal groups, J. Operator Theory
  73 (2015), arXiv:1309.2205.
* D. Berend, Multi-invariant sets on tori, Trans. AMS 280 (1983).
* C. Eckhardt, E. Gillaspy, P. McKenney, Finite decomposition rank for
  virtually nilpotent groups, arXiv:1706.04142.
* C. Eckhardt, J. Wu, Nuclear dimension and virtually polycyclic groups,
  arXiv:2408.07223 (Conjectures I and II).
* E. Kirchberg, W. Winter, Covering dimension and quasidiagonality,
  Internat. J. Math. 15 (2004).
* J. Rosenblatt, Invariant measures and growth conditions, Trans. AMS 193
  (1974); C. Chou, Elementary amenable groups, Illinois J. Math. 24 (1980).
