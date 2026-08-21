---
rg: 2
id: algebraic-compact-action-envelope-for-non-ce-relation
kind: claim
title: Embed the explicit non-CE relation factor in an effective compact-abelian algebraic crossed product
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that supplies the Manzoor relation factor inside another property-T relation factor; this requires the target relation to come from a compact-abelian algebraic action so its crossed product is a canonical semidirect-product group factor.
  perfect-zpc-irs-quantum-gap-game: that strengthens a game-value separation inside a restricted IRS strategy class; this asks for a trace-preserving von Neumann embedding into one Haar algebraic process and uses no finite-dimensional robust decoder.
---

For the explicit non-Connes-embeddable relation factor `N` supplied by
`non-ce-property-t-equivalence-relation-exists`, construct:

- a compact second-countable abelian group `K`;
- an effectively presented finitely generated group `Lambda` acting on `K`
  by continuous automorphisms; and
- a trace-preserving embedding

```text
N -> L^infinity(K) rtimes Lambda,                       (ACAE1)
```

such that `K-hat rtimes Lambda` is finitely generated and recursively
presented.  A preferred concrete form is a Haar linear subshift

```text
K <= (F_p^m)^Lambda
```

defined by effective finite-type or recursively enumerable linear local
constraints.  Then `algebraic-compact-action-group-factor-compiler` produces
a non-hyperlinear group, and Higman produces a finitely presented one.

The inclusion in `(ACAE1)` is essential: a non-CE quotient of an embeddable
crossed product gives no contradiction because Connes embeddability is not
known to pass to arbitrary quotients.

## Attempts

- **Haar is load-bearing.** An arbitrary shift-invariant measure does not
  Fourier-transform to a group von Neumann algebra.  The witness process must
  be linear-algebraic enough that the invariant measure is Haar.
- **Relation envelope is not yet algebraic.** The
  Chifan--Drimbe--Ioana/Manzoor property-T relation envelope gives an inclusion
  into a relation factor but does not provide a compact abelian base or an
  algebraic action.  No consequence for a discrete group follows until this
  extra structure is installed.
- **Source audit: the universal property-(T) construction is genuinely
  nonabelian.**  In Chifan--Drimbe--Ioana's proof the ambient factor is
  `Q=M_tilde^C rtimes_(beta,w) C`, where `M_tilde` is a nonabelian factor
  containing the input and `(beta,w)` is a cocycle action.  The paper also
  explicitly leaves embedding universality of group factors open.  See
  `cdi-property-t-envelope-has-nonabelian-base`.  Consequently the word
  "wreath-like" in that source cannot be read as an ordinary abelian-base
  wreath product, and its theorem supplies no hidden instance of `(ACAE1)`.
- **Unrestricted algebraic envelopes are exactly the main problem.**
  `unrestricted-algebraic-envelope-equals-nonhyperlinearity` shows
  that allowing an arbitrary non-CE source and arbitrary actor is equivalent
  to existence of a non-hyperlinear group (the reverse direction uses the
  trivial compact base).  The fixed `N`, effective presentation, and genuine
  module structure are therefore load-bearing, not cosmetic refinements.
- **ZPC/LCS opportunity and risk.** Finite-field constraints naturally define
  closed linear subshifts, avoiding the current robust groupification decoder.
  The unresolved step is to embed the non-CE GNS/relation algebra, not merely
  reproduce its scalar correlations.  Fourier-positivity identities of Haar
  algebraic processes give an early falsification test for each candidate
  game witness.
- **Finite cocycles allowed.** If the natural Pauli/LCS envelope is twisted by
  a finite scalar cocycle, `thom-central-corner-criterion` converts the
  selected twisted sector to a corner of a finite central extension.  This
  relaxes `(ACAE1)` without creating a separate compiler theorem.
- **Universal action-factor algebraization is false.**
  `haar-algebraic-actions-have-permutation-koopman-spectrum` proves that the
  Koopman representation of a Haar compact-abelian automorphism action is the
  permutation representation on `K-hat`; every measurable action factor has
  Koopman representation contained in that permutation representation.  For
  `Z`, this already excludes irrational rotations because the only point
  eigenvalues of a permutation unitary are roots of unity.  Thus one cannot
  obtain `(ACAE1)` by putting an arbitrary compact group structure on the
  existing atomless relation base.
- **Direct Haar-IRS realizations have an arithmetic fence.** For a finite set
  `F subset Lambda`, Haar probability that all elements of `F` fix the random
  point is either zero or the reciprocal of the index of the closed fixed
  subgroup.  For the preferred `F_p`-linear subshifts it is exactly zero or a
  power `p^(-r)`.  The Manzoor IRS must pass all of these cylinder tests before
  it can be realized directly as a Haar-linear stabilizer process.  No
  violating cylinder is currently known, so this is a falsification test, not
  a refutation.

These fences isolate the smallest live theorem more accurately.  It is not a
universal algebraization of p.m.p. actions.  One must either construct a
special non-CE Haar algebraic action natively, or produce a genuinely
non-Cartan/non-base-equivariant inclusion `(ACAE1)` in which the original
relation action is not a measurable factor of `K` and its normalizers are not
identified with the global `Lambda`-unitaries.

There is a stronger no-go for the preferred finite-type implementation.
`finite-type-linear-vfree-envelope-is-residually-finite`
uses the residual-finiteness theorem for finitely presented modules over
finite-field free-group algebras (Garrido--Jaikin-Zapirain, Proposition 5.3)
to prove that every finite-type linear subshift over a finitely generated
virtually free group has residually finite dual semidirect product.  Manzoor's
native acting group is virtually free.  Therefore a finite list of linear
local rules over that group always gives a sofic/hyperlinear crossed product
and can never contain `N`.  Within the native acting group, the linear-subshift
branch must use infinitely many r.e. relations producing a genuinely
non-residually-finite module; no finite constraint gadget can close the route.

Non-residuality is not sufficient.  The construction in
`nonresidual-linear-module-can-give-a-sofic-envelope` takes an effective
finitely generated infinite simple amenable quotient `F -> Q` and the cyclic
module `A=F_p[Q]`.  The module is recursively presented and an augmentation
difference `delta_q-delta_1` dies in every finite module quotient, so neither
`A` nor `A rtimes F` is residually finite.  Nevertheless

```text
1 -> A x ker(F->Q) -> A rtimes F -> Q -> 1
```

has sofic kernel and amenable quotient, hence `A rtimes F` is sofic.  The live
infinite-type module must therefore carry a genuinely nonsofic action/CE
obstruction, not merely lack separating finite invariant quotients.

In fact the native acting group is now completely ruled out, without any
finite-type hypothesis.  `abelian-by-virtually-free-groups-are-sofic` proves
that for every countable abelian module `A` and every finitely generated
virtually free group `Lambda`, the semidirect product `A rtimes Lambda` is
sofic: build `A rtimes F_r` by iterated HNN extensions over the amenable
subgroup `A`, then pass from a normal finite-index free subgroup to `Lambda`
by amenable-extension permanence.  Hence every compact-abelian Haar crossed
product with Manzoor's native virtually-free actor is Connes embeddable,
including every infinite-type/r.e. module and every proposed non-Cartan
placement inside that ambient algebra.  The route can survive only by
changing the acting group, not merely the module presentation.

The actor restriction is substantially stronger than “not virtually free.”
`haagerup-actors-cannot-host-property-t-algebraic-envelope` applies Popa's
relative property-H rigidity theorem: if `Lambda` is Haagerup, then
`L^infinity(K) rtimes Lambda` has property H relative to its abelian (hence
type-I) base, and it contains no relatively rigid `II_1` subalgebra.  Since
the target `N` is itself property `(T)`, **every Haagerup actor is ruled out**,
even for a genuinely non-Cartan embedding.  Any surviving replacement actor
must therefore be non-Haagerup; merely leaving the virtually-free class is not
enough.

The one-transformation spectral fence also sharpens.  By
`z-haar-algebraic-factors-have-lebesgue-plus-torsion-spectrum`, every factor
of a Haar algebraic `Z`-action has maximal spectral type dominated by circle
Haar measure plus atoms at roots of unity.  Thus singular-continuous Gaussian
actions cannot be algebraized this way: the Gaussian first chaos already
violates the required spectral type.  Gaussian compactification supplies no
universal route around the permutation-spectrum obstruction.  More exactly,
`gaussian-action-haar-algebraic-factor-criterion` proves for every countable
actor that a Gaussian action is a Haar algebraic action factor **if and only
if** its defining orthogonal representation is contained in a countable
permutation representation.  Hence the Gaussian route is now fully reduced
to a representation-containment test; it has no additional nonlinear
compactification freedom.

There is a least-circular explicit way to meet the non-Haagerup actor
requirement: replace the native virtually-free source actor `Gamma_0` by
`Gamma_0 x SL_3(Z)`.  This still does nothing by itself.
`nonhaagerup-spectator-must-couple-nonamenably` proves that for every abelian
dual module `A`, if the `SL_3(Z)` direction has amenable image in `Aut(A)`,
then `A rtimes (Gamma_0 x SL_3(Z))` is sofic.  Since every amenable quotient
of `SL_3(Z)` is finite, a viable module must carry an infinite, nonamenable
`SL_3(Z)` image.  Trivial/finite actions and an independent algebraic
Bernoulli spectator are therefore barren.  The first genuinely new
constructive target is a **mixed** module on which the commuting
`Gamma_0` and `SL_3(Z)` directions interact; merely appending a known
non-Haagerup group cannot transport the Manzoor/CDI inclusion.

In fact property `(T)` removes even the proposed genuinely mixed escape.
`haagerup-factor-direction-strips-from-property-t-envelope` views the total
crossed product as

```text
(L^infinity(K) rtimes SL_3(Z)) rtimes Gamma_0.
```

Haagerup Fourier multipliers for the virtually-free `Gamma_0` direction,
combined with rigidity of the embedded property-`(T)` factor, force that
factor to intertwine into `L^infinity(K) rtimes SL_3(Z)`.  Therefore if the
total mixed crossed product contains the fixed non-CE `N`, the `SL_3(Z)`-only
crossed product is already non-CE and `K-hat rtimes SL_3(Z)` is already
non-hyperlinear.  This applies to every commuting module action, including
infinite nonamenable `SL_3(Z)` image, and makes no Cartan assumption on the
embedding.  Hence the Manzoor direct factor cannot carry the obstruction at
all: a successful module over `Gamma_0 x SL_3(Z)` is automatically a solution
after restriction to `SL_3(Z)`.

Changing the actor by ordinary induction or coinduction also does not install
the missing algebraic base.  `coinduction-preserves-but-cannot-create-algebraic-envelope`
shows that compact algebraic coinduction from `H<Lambda` does give a
trace-preserving inclusion

```text
L^infinity(K_0) rtimes H
    -> L^infinity(K_0^(Lambda/H)) rtimes Lambda,
```

but only when the original `H`-action on `K_0` was already Haar algebraic.
The usual induced base-coset corner is instead a corner of a **semifinite**
crossed product with counting measure on `Lambda/H`; at infinite index there
is no invariant probability version.  This is not a defect of the product
model.  `infinite-index-canonical-subgroup-corner-is-impossible` proves in
every finite crossed product that a positive `H`-invariant projection whose
canonical Fourier compression kills every `g notin H` would have infinitely
many orthogonal equal-trace translates.  Therefore no positive-trace
canonical coset corner can import `N` at infinite index.  The remaining
change-of-actor freedom is genuinely non-Cartan: its image cannot be obtained
by cutting the global `Lambda` unitaries down to the old actor.

The simplest mixed module for `Gamma_0 x SL_3(Z)` is also barren.  Given a
homomorphism `phi:Gamma_0 -> SL_3(Z)`, take the finite lamp module on the
cosets of its graph.  `graph-coset-mixed-module-is-sofic` proves that the
graph is automatically separable: residual finiteness of `SL_3(Z)` separates
`(g,h)` from the graph whenever `h != phi(g)`.  The coset action is therefore
sofic, and so is its generalized wreath group.  This remains true when the
`SL_3(Z)` image is infinite and nonamenable, so the preceding necessary
coupling test is not sufficient.  The mixed-module target must now use a
nonseparable stabilizer or leave the permutation/coset-module class.  Since
`Gamma_0` is virtually free/LERF, the same proof handles every finitely
generated stabilizer whose projection to `Gamma_0` is injective.  Thus a
finitely generated nonseparable stabilizer must have a nontrivial vertical
intersection with `SL_3(Z)`; otherwise the only remaining coset option is an
infinitely generated stabilizer.
