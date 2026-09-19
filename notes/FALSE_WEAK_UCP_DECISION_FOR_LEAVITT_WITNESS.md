# Weak ucp-stability exactly decides hyperlinearity of the Leavitt witness

Date: 2026-08-12

## 1. Outcome

Put

```text
L=L_(F_2)(1,2),       Q=EL_4(L).                       (WUD1)
```

The existing algebraic part of the project proves that `Q` is an infinite
finitely generated simple group with property `(T)`, and that `Q` is
nonsofic.  In particular, `Q` is not residually finite.

Dogon's Proposition 1.11 in *Flexible Hilbert--Schmidt stability versus
hyperlinearity for property (T) groups*, Math. Z. 305 (2023), Article 58,
then gives an exact analytic decision:

**Theorem 1.**  The following are equivalent.

1. `Q` is hyperlinear.
2. `Q` admits a hyperlinear approximation.
3. `Q` is not weakly ucp-stable.
4. There exists a hyperlinear nonsofic group, witnessed by this specific
   group `Q`.

Equivalently,

```text
Q weakly ucp-stable  <=>  Q nonhyperlinear.            (WUD2)
```

Thus weak ucp-stability of this one explicit group selects exactly the same
fork as flexible Hilbert--Schmidt stability of its Steinberg cover, but it
does so directly on the simple quotient.

## 2. Proof of the decision theorem

The equivalence of (1) and (2) is the standard sequential formulation of
hyperlinearity for countable groups.  Since `Q` is already nonsofic, (1) and
(4) are equivalent.

Suppose (1) holds.  If `Q` were weakly ucp-stable, Dogon's Proposition 1.11
would apply because `Q` has property `(T)`: a hyperlinear property-`(T)` group
which is weakly ucp-stable is residually finite.  This contradicts the fact
that the infinite simple group `Q` is not residually finite.  Hence (1)
implies (3).

Conversely, failure of weak ucp-stability is witnessed by a hyperlinear
approximation

```text
phi_n:Q->U(d_n)                                         (WUD3)
```

for which no sequence of the prescribed ucp compressions exists.  In
particular, `(WUD3)` exists.  Existence of a hyperlinear approximation is
exactly hyperlinearity of `Q`, so (3) implies (2).  This proves the theorem.

The last implication is elementary but important.  Weak ucp-stability is
defined by a universal statement **over hyperlinear approximations**.  A
nonhyperlinear group has no such approximations and is therefore weakly
ucp-stable vacuously.  Consequently `(WUD2)` does not assert that the
nonhyperlinear branch has a positive lifting mechanism.

## 3. Comparison with the Steinberg-cover decision

Let

```text
U=St_5(L).                                              (WUD4)
```

The stability fork already established in `notes/NOTEPAD.md` says

```text
Q hyperlinear
 <=> U is not flexibly Hilbert--Schmidt stable.         (WUD5)
```

Combining Theorem 1 with `(WUD5)` gives

```text
U flexibly HS-unstable
 <=> Q weakly ucp-unstable
 <=> Q hyperlinear and nonsofic.                        (WUD6)
```

These are two genuinely different instability problems:

* the first asks for an arbitrary nontrivial normalized-HS asymptotic
  representation of the minimally almost-periodic central cover `U`;
* the second asks for a trace-separating hyperlinear approximation of `Q`
  which has no infinite-dimensional ucp correction.

For this particular `Q`, the second non-correction is automatic once a
hyperlinear approximation exists, by property `(T)` and non-residual
finiteness.  Therefore the constructive content on either side of `(WUD6)`
is still exactly the production of matrix microstates, not a separate
failure-of-lifting estimate.

## 4. What the central-extension theorem adds

Dogon's main central-extension theorem is stronger than the flexible
HS-stability result that motivated it: under its cohomological hypotheses,
weak ucp-stability of the quotient forces nonhyperlinearity of the central
extension.  Its proof isolates an especially useful FALSE-side certificate.
For a property-`(T)` group `Gamma`, it suffices to construct cocycles

```text
c_n in Z^2(Gamma,T),       [c_n]!=0,                   (WUD7)
c_n(g,h)->1 for every fixed g,h,                       (WUD8)
L_(c_n)(Gamma) is Connes embeddable.                   (WUD9)
```

The canonical twisted regular unitaries have zero trace off the identity.
Equations `(WUD8)--(WUD9)` therefore give a trace-separating matrix
approximation, while `(WUD7)` makes the projective Kazhdan lemma obstruct a
ucp correction.  For `Gamma=Q`, such a family would prove Theorem 1(1), and
hence FALSE, directly.

This criterion is not currently a construction.  Obtaining all the twisted
CE algebras from a common hyperlinear central extension, via Thom's theorem,
would already provide a hyperlinear nonsofic central cover.  Moreover the
known Steinberg cover `U` is universal and superperfect, so its second
homology does not provide another central layer on which to iterate the
argument.

For this particular `Q`, there is a stronger scope correction.  The
injective prefix endomorphism

```text
kappa:Q->Q
```

induces zero on `H_2(Q,Z)`.  By naturality of the universal-coefficient
identification, every circle-valued cocycle becomes a coboundary on
`kappa(Q)`.  Hence every twisted regular algebra `L_c(Q)` contains a
trace-preserving copy of the untwisted algebra `L(Q)`.  Consequently

```text
L_c(Q) Connes embeddable  ==>  Q hyperlinear            (WUD10)
```

for each cocycle separately.  Thus `(WUD7)--(WUD9)` is an exact decision
certificate but cannot be used as an easier preliminary CE problem: one
embeddable member already solves the target.  See
`FALSE_PREFIX_TWISTED_SUBALGEBRA_RIGIDITY.md` for the proof and for the
parallel phase-death statement on the universal cover.

## 5. Exact scope of the four stability inputs

The recent results now divide the unresolved matrix sector cleanly.

1. Dogon--Vidick polynomially corrects arbitrary normalized-HS approximate
   representations on every finite-abelian lamplighter window.
2. Burton--Chaudkhari--Juschenko--Muliarchyk corrects trace-separated
   hyperlinear approximations of every amenable group to same-dimensional
   sofic-induced approximations.
3. Dogon--Vigdorovich and the character-rigidity results control amenable
   tracial limits and robust spectral gaps, but do not create a nonamenable
   Connes-embeddable trace.
4. Dogon's weak ucp theorem makes any such trace-separating model of `Q`
   automatically non-ucp-liftable.

Consequently the unresolved step is not to prove instability after finding
microstates.  It is to find the microstates themselves.  They cannot be
localized in an amenable cyclic sector and, for the relative-wall candidate,
cannot arise from flexibly liftable finite-dimensional representations.

## 6. Source pins

* Alon Dogon, *Flexible Hilbert--Schmidt stability versus hyperlinearity for
  property (T) groups*, Math. Z. 305 (2023), Article 58, especially
  Proposition 1.11 and Theorem 3.1.
* Alon Dogon and Itamar Vigdorovich, *Connections between hyperlinearity,
  stability and character rigidity for higher rank lattices*,
  arXiv:2506.20843.
* Alon Dogon and Thomas Vidick, *Polynomial Hilbert--Schmidt stability of the
  lamplighter group*, arXiv:2607.20135.
* Peter Burton, Maksym Chaudkhari, Kate Juschenko, and Kyrylo Muliarchyk,
  *Hyperlinear approximations to amenable groups come from sofic
  approximations*, arXiv:2311.09202.
