# Ioana--Drimbe rigidity does not construct the three-moment Schreier system

Date: 2026-08-11

## 1. Exact status

For the actual Kun--Thom induced transition system at clock order `M_k`,
write

`R_(*,k)=max_(s in S)(average_x |r_k(x,s)|_(M_k)^2)^(1/2)`,

`A_(*,k)=max_(s in S) average_x |a_k(x,s)|_(M_k)`.       `(IDS1)`

The three quantities that must vanish are

`R_(*,k)/M_k`,

`A_(*,k)/M_k`,

`R_(*,k)A_(*,k)/M_k`.                                  `(IDS2)`

No transversal sequence for the actual system satisfying `(IDS2)` has
been constructed.  In particular, neither Ioana's profinite cocycle
superrigidity theorem nor Drimbe's coinduced-action theorem supplies such a
sequence.

This is not merely a missing citation.  For the scalar primitive-clock
realization, `FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md` proves
that every transversal has

`max_(s in S) average_x |d_s(x)|_(M_k)`
` >=(kappa^2/(4 pi))M_k`.                               `(IDS3)`

Hence whichever scalar Weyl coordinate carries the primitive holonomy has
one of the first two ratios in `(IDS2)` bounded away from zero.  The scalar
three-moment target is therefore false, not merely uncomputed.

The surviving target is a base-dependent paired Fourier/Frobenius system
in which the primitive holonomy is absorbed by a change of polarization or
by higher-incidence cancellation and is not itself either scalar transition
coordinate in `(IDS1)`.

## 2. What Ioana's theorem actually gives

Ioana considers one measurable cocycle

`beta:A times X -> Lambda`                              `(IDS4)`

from a **free ergodic** profinite action of a property-`(T)` group (or the
stated relative property-`(T)` generalization) into one fixed countable
target `Lambda`.
The theorem makes `(IDS4)` cohomologous to a cocycle factoring through one
finite quotient of `X`.

Applied to a hypothetical fixed countable
`BS(1,p+1)`-valued lift of all our transition systems, this would reduce the
positive-generator range to a fixed finite set.  After a constant
stable-letter conjugation clears its finitely many denominators, cylinder
approximation of the transfer function gives finite gauges with

`R_(*,k)=O(1)`, `A_(*,k)=O(1)`.                         `(IDS5)`

That conditional implication is proved in
`FALSE_IOANA_COHERENT_SCHREIER_LIFT_CRITERION.md`.

There is first an action-scope gap.  The natural inverse limit of coset
actions retains the amenable stabilizer and is nonfree, whereas the quoted
theorem assumes freeness.  No free profinite realization carrying the same
transition tables has been constructed, and no nonfree replacement theorem
is being invoked here.

Even after postulating such a free realization, the coherent lift is
precisely what is absent.  The actual data are a
sequence

`beta_k:A times X_k -> B_k`                            `(IDS6)`

with growing finite targets.  Applying Ioana separately to each `beta_k`
produces transfer maps and factorization levels depending on `k`; it gives
no Archimedean control on centered coordinates modulo `M_k`.  Passing to
the inverse-limit target replaces `(IDS6)` by a cocycle into an uncountable
profinite group, outside the quoted countable-target theorem.  Even a
finite-stage conclusion in that compact target would not imply `(IDS2)`,
because a fixed profinite element can have centered reductions of order
`M_k`.

Equation `(IDS3)` goes further: in the primitive scalar system, a coherent
lift, compatibility with the prescribed clock coordinate, and the bounded
chart conclusion `(IDS5)` cannot all coexist.

## 3. What Drimbe's theorem changes, and what it does not

Drimbe proves cocycle superrigidity for a broad class of **coinduced pmp
actions**.  Under his hypotheses, a cocycle with values in a target from
the class `U_fin` is cohomologous to a homomorphism.  Importantly, `U_fin`
contains every compact Polish group, not only countable groups.

This target enlargement still does not help the clock construction.  The
theorem in `FALSE_DRIMBE_COMPACT_CLOCK_UNTWISTING_NO_GO.md` proves that the
natural compact inverse-limit clock group

`Z_p semidirect_(1+p) Z_p`

is amenable and torsion-free.  A homomorphism from a property-`(T)` group
into it has finite image and is therefore trivial.  Hence every such compact
clock cocycle on a Drimbe coinduced action is a coboundary.  Its finite
reductions can be gauged to zero, but their primitive fold holonomy is then
also zero.

It does not solve the present transition problem for three independent
reasons.

1. Coinduction of a pmp action is not the same operation as choosing
   transversals in the finite Shapiro/Schreier representation bundle.  The
   theorem starts with a genuine measurable cocycle; it does not construct
   a coherent lift of the changing finite transition tables `(IDS6)`.

2. Levelwise application again gives unrelated transfers and homomorphisms
   as `k` varies.  The theorem contains no estimate comparing their centered
   coordinates to `M_k`.

3. For an arbitrary compact target, cohomology to a homomorphism is only
   topological/algebraic information and need not control Archimedean sizes.
   For the natural inverse-limit metacyclic clock target, however, the
   homomorphism is forced to be trivial.  This is stronger but sterile: it
   kills the primitive fold together with all transition moments.

Thus Drimbe can replace the rigidity engine only **after** one has built a
single coherent cocycle in an appropriate fixed target.  It cannot supply
the missing cocycle or the desired transversals.  For the obvious compact
clock target, it proves that the required coherent primitive cocycle does
not exist.

## 4. Exact endgame statement

The real remaining FALSE theorem is not `(IDS2)` for the already excluded
scalar principal bundle.  It is the following nonliftable paired version.

Construct approximate basepoint maps on the actual finite external
Schreier orbits which

1. satisfy every fixed positive square-zero, elementary, external
   covariance, and amalgam relation with normalized-Hilbert--Schmidt defect
   tending to zero;
2. retain a fixed positive marked fold energy; and
3. realize the external transition law through base-dependent Fourier
   polarizations or higher-incidence cancellation, rather than a primitive
   scalar coordinate.

By `FALSE_EQUIVARIANT_FIBER_FUNCTOR_STABILIZER_REDUCTION.md`, all fiber
variables reduce to basepoint stabilizer equations and a relative-holonomy
table.  By `FINITE_REPRESENTATION_MATCHING_BARRIER.md`, the resulting maps
cannot be uniformly corrected to honest finite-dimensional vertex
representations.  Quantitatively, a marked gap `c` and vanishing edge error
force distance at least

`c/(2+4/kappa)`                                          `(IDS7)`

from every honest pair on the finite Kazhdan/fold window.

That is the genuine finite-stage object still to be constructed.  Until it
is constructed, the three real transition numbers have not been proved to
vanish and FALSE is not established.
