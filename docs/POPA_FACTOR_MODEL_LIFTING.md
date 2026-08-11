# The projective phase bundle is Popa's factor: what must actually lift

Date: 2026-08-11.

This note audits the projective-shift reformulation in
`docs/TRUE_HAAR_PHASE_KERNEL.md`, `(HPK9cy)--(HPK9dh)`.  The main conclusion
is a correction of scope:

> The required finite theorem is **not** model-surjectivity of the Popa
> factor map.  It is an existential, relative, Hamming-exact selection of a
> finite-torsion cocycle sector.  That sector need not be cohomologically
> zero.

Austin's Popa-factor examples show that model-surjectivity is false even for
very classical sofic groups.  They do not obstruct the finite-phase selection
needed here: their nonliftable sectors are themselves represented by
finite-image stabilizer characters.

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
factor.  More importantly, every nonzero sector in his construction is also
finite-phase.  Each stabilizer `H_n` has property `(T)` (it has finite index
in `Q`), so its finitely generated abelianization is finite.  By `(PFL5b)`,
every stabilizer character therefore has finite image.  The projective model
may fail to lift to a vertex potential while still defining an exact finite
circle extension, which is all phase completion asks for.

Therefore the notions relevant here compare as follows.

| property | quantifier on target models | quality of the lift |
|---|---|---|
| Austin model-surjectivity | every good model sequence | global `T`-valued vertex potential, up to average-metric error |
| phase completion `(HPK18)` | existence of one sequence compatible with the given base colors and Haar joining | possibly nontrivial finite-circle bundle; cocycle equality off `o(1)` vertices |

Neither phrase should be substituted for the other.  The phase requirement
is weaker in quantification, allows nonzero torsion holonomy, and is stronger
in its demand for equality away from a small set.

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
`docs/TRUE_HAAR_PHASE_KERNEL.md` finishes the sofic approximation.  End
proof.

This lemma is only a sufficient special case.  It is useful for a quotient
circle cocycle after the phase-kernel data have been separated, but it is far
too strong for the full monomial cocycle: a nontrivial kernel element has
asymptotically trivial base permutation and a Haar-distributed diagonal
phase, so it cannot be close to a coboundary.  The general completion must
retain such phases in a nonzero finite-torsion sector.

The exact finite classification is as follows.  For a transitive exact
finite action `V=Q/H`, a circle cocycle class has a `mu_m`-valued
representative if and only if its stabilizer character `(PFL5a)` has image in
`mu_m`.

**Proof.**  Necessity follows by restricting a `mu_m`-valued cocycle to the
stabilizer.  Conversely, choose a section `tau:Q/H->Q` and put

`kappa(q,v)=tau(qv)^(-1) q tau(v) in H`.              `(PFL10a)`

If `chi_a(H) subset mu_m`, then

`z_q(v)=chi_a(kappa(q,v))`                           `(PFL10b)`

is a `mu_m`-valued cocycle in the class of `a`; the Schreier identity for
`kappa` proves the cocycle equation.  End proof.

Thus the relevant sector condition is **finite stabilizer image**, not
trivial stabilizer image.  Austin's property-`(T)` example sharply separates
the two conditions: every sector has finite stabilizer image, while some
sectors stay uniformly far from the trivial one.

## 5. Revised live gate

For the factor `Phi_eta:X->P_Q` coming from a monomial hyperlinear model, the
remaining task is:

> Select finite models of the already-sofic base action, with the prescribed
> `Phi_eta` colors and relatively-Haar statistics, whose phase near-cocycle is
> `o(1)` from an exact cocycle with values in some finite circle group
> `mu_(m_n)`.  The cohomology sector may be nonzero and `m_n` may grow.

Austin's theorem warns that arbitrary good models need not lift through
`T^(V_n)`.  Its finite stabilizer calculation also proves that this warning is
not itself an obstruction to `(HPK18)`: those nonliftable sectors can still be
finite-phase.  What remains special to the evaluated extension cocycle and
Haar character field is the approximation by **some** finite-image sector.

For a fixed finite window `F`, let `Z^1_fin(sigma_n,F)` denote all families
`z_g:V_n->mu_m`, for any finite `m`, which obey the phase-cocycle identity
wherever the base chart obeys multiplication on `F`.  The useful sector
distance is

`kappa_n^fin(F)=inf_(z in Z^1_fin(sigma_n,F))
                 max_(g in F)||c_(n,g)-z_g||_2`.     `(PFL11)`

The exact remaining assertion is `kappa_n^fin(F)->0` along one compatible
model sequence for every finite `F`, with the Haar kernel and trace statistics
retained.  The zero-sector lemma treats only the subfamily of quantized
coboundaries.  A TRUE proof may use arbitrary finite stabilizer characters;
a FALSE construction would have to keep `(PFL11)` bounded away from zero,
not merely stay away from `B^1`.

## Sources

* Tim Austin, [*The geometry of model spaces for probability-preserving
  actions of sofic groups*](https://arxiv.org/abs/1512.01500), especially
  Definition 3.1, Theorems A, C, D, and Section 6.2.
* Liviu Paunescu, [*On Sofic Actions and Equivalence
  Relations*](https://arxiv.org/abs/1002.0605), especially Section 3 for the
  surrounding fact that soficity of all free actions of an arbitrary sofic
  group is itself open.
