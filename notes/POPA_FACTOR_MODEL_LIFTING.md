# The projective phase bundle is Popa's factor: what must actually lift

Date: 2026-08-11.

This note audits the projective-shift reformulation in
`notes/TRUE_HAAR_PHASE_KERNEL.md`, `(HPK9cy)--(HPK9dh)`.  The main conclusion
is a correction of scope:

> The required finite theorem is **not** model-surjectivity of the Popa
> factor map.  It is an existential, relative, Hamming-exact selection of a
> finite-phase cocycle.  On a fixed finite chart torsion cocycles are dense
> in all exact circle cocycles, so the real issue is closeness to the exact
> cocycle locus, not the cohomology sector.

Austin's Popa-factor examples show that model-surjectivity is false even for
very classical sofic groups.  They do not obstruct the finite-phase selection
needed here: Austin's bad models are already exact cocycles, and exact finite
charts can be approximated by torsion cocycles regardless of their sector.

## 1. Identification with the Popa factor

Let `Q` be a countable group, let

`P_Q = T^Q/T_diag`,

and let `pi:T^Q -> P_Q` be the quotient by diagonal scalar multiplication.
Both spaces carry the right shift.  This is exactly the Popa factor map used
by Austin.

For a finite symmetric generating set `S`, Austin uses the gradient model

`D:T^Q -> T^(S times Q)`,
`D(f)_(s,g)=f(sg)f(g)^(-1)`.                         `(PFL1)`

The kernel of `D` is `T_diag`, so its compact image `Z` is equivariantly
isomorphic to `P_Q`.  Under this isomorphism, the universal cocycle

`c_q([f])=f(q)f(1)^(-1)`                            `(PFL2)`

from `(HPK9da)` is the usual coordinate-difference cocycle of the Popa
factor.  Thus the bundle in `(HPK9dh)` is not merely analogous to Popa's
factor: it is the same factor map.

## 2. Universal model-surjectivity is false

Austin proves the following.  Let `Q` be an infinite residually finite group
with property `(T)`.  There is a sofic approximation `Sigma` for which:

1. the Bernoulli system `(T^Q,m^Q)` has connected model spaces;
2. its Popa factor `(P_Q,m_P)` does not have connected model spaces; and
3. a model-surjective factor of a system with connected model spaces must
   again have connected model spaces.

Consequently

`pi:(T^Q,m^Q) -> (P_Q,m_P)`                         `(PFL3)`

is **not** model-surjective relative to that `Sigma`.

The finite obstruction is completely explicit.  Austin chooses finite
Schreier graphs `Gamma_n=(V_n,E_n)`.  On such a graph, the finite shadow of
`pi` is

`d:T^(V_n) -> T^(E_n)`,                             `(PFL4)`

whose image is the group `B^1(Gamma_n,T)` of coboundaries.  Good Popa-factor
models occur in every coset of `B^1` inside `Z^1(Gamma_n,T)`.  The chosen
graphs have nonzero `H^1=Z^1/B^1`, and property `(T)` gives a constant
`r>0` separating every nonzero coset from `B^1`.  Hence some statistically
correct projective models stay a macroscopic distance from every lift.

This is precisely the sort of global carry sector that the phase analysis
encountered independently.  It rules out any argument of the form

`every good projective model has a coherent lift`.   `(PFL5)`

There is also a direct stabilizer description.  On one transitive finite
`Q`-set `V=Q/H`, an exact circle cocycle `a` determines

`chi_a:H->T`,  `chi_a(h)=a_h(H)`.                   `(PFL5a)`

The cocycle identity makes `chi_a` a character.  It is unchanged by adding a
coboundary, and it vanishes exactly when `a` is a coboundary.  Indeed, if
`chi_a=1`, define `b(gH)=a_g(H)`.  This is well-defined, and the cocycle
identity gives `a_q(v)=b(qv)b(v)^(-1)`.  Orbit by orbit, this is the concrete
Shapiro identification

`H^1(Q action V,T) = product_(orbits Q/H) Hom(H,T)`. `(PFL5b)`

Thus the nonliftable Popa sectors are precisely stabilizer-character sectors.
Austin arranges nontrivial characters by choosing stabilizers with nontrivial
abelianization.

This also shows why essential freeness of the limiting action does not force
the coboundary sector.  In Austin's sofic approximation every fixed
nonidentity `q in Q` eventually has no fixed vertices, but the stabilizers
`H_n` still have characters on elements whose word length escapes to
infinity.  Those global characters remain a uniform distance from `B^1`.
Slow tensor amplification, which kills fixed points for each fixed word,
therefore cannot by itself force the phase sector to be zero.

## 3. Why this does not refute the needed lifting statement

Model-surjectivity quantifies over **every** convergent sequence of good
target models and asks for a lift by a global vertex potential in `T^(V_n)`.
Soficity of the relatively-Haar pullback only needs **one** compatible
finite circle bundle.  Such a bundle may have nontrivial finite holonomy and
therefore need not come from a global potential.

In Austin's example the zero sector `B^1(Gamma_n,T)` is still present.  In
fact the pushforward of Haar measure on `T^(V_n)` under `(PFL4)` is supported
entirely on liftable models and converges locally to Haar measure on the Popa
factor.  More importantly, the nonzero models used to disconnect the target
are elements of `Z^1(Gamma_n,T)` already.  They therefore have zero distance
from the exact cocycle locus even though they stay a uniform distance from
`B^1`.  Section 4 below shows that every such exact finite-chart cocycle can
be approximated by finite-phase exact cocycles.  (In Austin's particular
construction one can say more: the finite-index property-`(T)` stabilizers
have finite abelianization, so their classes already have finite-image
representatives.)

Therefore the notions relevant here compare as follows.

| property | quantifier on target models | quality of the lift |
|---|---|---|
| Austin model-surjectivity | every good model sequence | global `T`-valued vertex potential, up to average-metric error |
| phase completion `(HPK18)` | existence of one sequence compatible with the given base colors and Haar joining | proximity to any exact cocycle, followed by torsion approximation and equality off `o(1)` vertices |

Neither phrase should be substituted for the other.  The phase requirement
is weaker in quantification, allows arbitrary cohomology sectors, and is
stronger in its demand for equality away from a small set.

## 4. A zero-sector rounding lemma (one sufficient case)

The distinction yields a useful positive finite criterion.  Let `V_n` be
finite sets, let `sigma_(n,g)` be permutation charts, and let
`c_(n,g):V_n->T` satisfy the approximate phase-cocycle law

`c_(n,h)(v)c_(n,g)(sigma_(n,h)v) ~= c_(n,gh)(v)`     `(PFL6)`

in normalized `L^2` on every fixed window.  Suppose there are functions
`b_n:V_n->T` such that, for every fixed `g`,

`||c_(n,g) - d b_n(g)||_2 -> 0`,
`d b_n(g)(v)=b_n(sigma_(n,g)v)b_n(v)^(-1)`.          `(PFL7)`

Then the phase data admit the finite-phase completion required by
`(HPK13)--(HPK15)`.

**Proof.**  Choose `m_n->infinity` sufficiently slowly and round every value
of `b_n` to a nearest element of `mu_(m_n)`, obtaining `beta_n`.  Put

`z_(n,g)(v)=beta_n(sigma_(n,g)v)beta_n(v)^(-1)`.     `(PFL8)`

The nearest-root estimate gives

`||d b_n(g)-z_(n,g)||_2 <= 2 pi/m_n`.                `(PFL9)`

Thus `(PFL7)` implies `||c_(n,g)-z_(n,g)||_2->0` on
every fixed window.  Wherever

`sigma_(n,g)sigma_(n,h)v=sigma_(n,gh)v`,

the factors in `(PFL8)` telescope and give the exact identity

`z_(n,h)(v)z_(n,g)(sigma_(n,h)v)=z_(n,gh)(v)`.       `(PFL10)`

Hence phase multiplication fails only where the base permutation chart
fails.  Finally normalized monomial traces change by at most the normalized
`L^1` distance, which is bounded by the `L^2` distance.  Therefore the trace
limits of the original monomial data are retained.  Equations
`(PFL8)--(PFL10)` are exactly `(HPK13)--(HPK15)`, and Theorem 4 of
`notes/TRUE_HAAR_PHASE_KERNEL.md` finishes the sofic approximation.  End
proof.

This lemma is only a sufficient special case.  It is useful for a quotient
circle cocycle after the phase-kernel data have been separated, but it is far
too strong for the full monomial cocycle: a nontrivial kernel element has
asymptotically trivial base permutation and a Haar-distributed diagonal
phase, so it cannot be close to a coboundary.  The general completion must
retain such phases in a nonzero finite-torsion sector.

There is a general replacement for the zero-sector hypothesis.  Fix one
finite permutation chart and one finite multiplication window, and let `C`
be the set of all circle-valued phase tables satisfying the required cocycle
equalities wherever the base permutations multiply correctly.  Then `C` is
a closed subgroup of a finite-dimensional torus.  Hence

`closure(C_tor)=C`,                                  `(PFL10a)`

where `C_tor` denotes the phase tables whose finitely many coordinates all
belong to one finite circle group `mu_M`.  Indeed, a closed subgroup of a
finite-dimensional torus is a compact abelian Lie group, isomorphic to a
torus times a finite abelian group up to a finite quotient, and its torsion
points are dense.  This is the same torsion-density step used in
`(CS6)--(CS8)` of `notes/NOTEPAD.md`.

Consequently, once an approximate phase table is `o(1)` from **any** exact
circle cocycle, it is also `o(1)` from an exact finite-phase table.  No
control of its cohomology class is necessary.

The exact finite classification is as follows.  For a transitive exact
finite action `V=Q/H`, a circle cocycle class has a `mu_m`-valued
representative if and only if its stabilizer character `(PFL5a)` has image in
`mu_m`.

**Proof.**  Necessity follows by restricting a `mu_m`-valued cocycle to the
stabilizer.  Conversely, choose a section `tau:Q/H->Q` and put

`kappa(q,v)=tau(qv)^(-1) q tau(v) in H`.              `(PFL10b)`

If `chi_a(H) subset mu_m`, then

`z_q(v)=chi_a(kappa(q,v))`                           `(PFL10c)`

is a `mu_m`-valued cocycle in the class of `a`; the Schreier identity for
`kappa` proves the cocycle equation.  End proof.

This class-preserving statement explains the stabilizer holonomy, but it is
still stronger than phase completion needs.  If `chi_a` has infinite image,
torsion characters approximate it on every finite set of stabilizer carries;
equivalently `(PFL10a)` approximates the whole cocycle by finite-phase
cocycles in nearby classes.  Austin's example sharply separates all three
notions: some sectors are uniformly far from `B^1`, all are exact, and all
are eligible for finite-phase approximation.

## 5. Revised live gate

For the factor `Phi_eta:X->P_Q` coming from a monomial hyperlinear model, the
remaining task is:

> Select finite models of the already-sofic base action, with the prescribed
> `Phi_eta` colors and relatively-Haar statistics, whose phase near-cocycle is
> `o(1)` from the exact circle-cocycle locus.  Torsion density then replaces
> the nearby exact cocycle by one with values in some `mu_(m_n)` without
> changing the asymptotics.

Austin's theorem warns that arbitrary good models need not lift through
`T^(V_n)`, but its bad models are already exact cocycles.  Thus that warning
is orthogonal to `(HPK18)`.  What remains is a uniform cocycle-stability
problem: raw `L^2` multiplicative defect must control distance to the exact
cocycle locus on the chosen growing charts.

For a fixed finite window `F`, let `C_n(F)` be the closed subgroup of all
circle phase tables obeying the phase-cocycle identity wherever the base
chart obeys multiplication on `F`.  The useful distance is

`kappa_n(F)=dist_(L^2)(c_n,C_n(F))`.                 `(PFL11)`

By `(PFL10a)`, this equals the infimum of the distance to exact finite-phase
tables.  The exact remaining assertion is `kappa_n(F)->0` along one
compatible model sequence for every finite `F`, with the Haar kernel and
trace statistics retained.  This is precisely qualitative `T`-valued
degree-one cocycle stability `(CS1)`, already isolated and proved sufficient
in `(CS1)--(CS8)` of `notes/NOTEPAD.md`.  A TRUE proof must arrange that
stability (possibly after changing charts); a FALSE construction would have
to keep `(PFL11)` bounded away from zero despite vanishing raw cocycle defect.
Merely occupying a nonzero Popa cohomology sector proves neither outcome.

## Sources

* Tim Austin, [*The geometry of model spaces for probability-preserving
  actions of sofic groups*](https://arxiv.org/abs/1512.01500), especially
  Definition 3.1, Theorems A, C, D, and Section 6.2.
* Liviu Paunescu, [*On Sofic Actions and Equivalence
  Relations*](https://arxiv.org/abs/1002.0605), especially Section 3 for the
  surrounding fact that soficity of all free actions of an arbitrary sofic
  group is itself open.
