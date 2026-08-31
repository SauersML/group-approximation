---
rg: 2
id: property-t-does-not-kill-boolean-fiber-holonomy
kind: claim
title: Property (T) does not kill exact Boolean-fiber holonomy; canonical trace regularizes only fixed finite types
distinct_from:
  boolean-atom-overlap-spatializes-arrows-but-full-corners-stay-diffuse: that proves pairwise transport of whole Boolean atoms and leaves a diffuse unitary cocycle; this classifies that cocycle by stabilizer holonomy, gives an exact property-(T) obstruction, and proves a positive theorem when the holonomy group is fixed and its conditional character is canonical.
  finite-schreier-holonomy-is-the-lamp-gauge-obstruction: that gives a finite-cycle compatibility criterion for supplied block normalizers; this identifies the remaining cycle data as a representation and separates large exact holonomy from perturbative additive cocycles.
  el-r-polynomial-robust-spectral-gap: that controls almost invariant vectors by property-(T) spectral gap; this shows why such a gap cannot force a macroscopic exact unitary representation to be scalar or monomial.
  phase-free-cartan-observables-force-joint-lamp-targets: that extracts point permutations after a common rank-one masa is supplied; this quantifies when canonical mixed traces themselves manufacture a monomial basis inside a fixed finite holonomy fiber.
  coset-wreath-wall-survives-full-commutant-corners: that preserves every fixed Boolean atom at positive asymptotic density; this combines that density with the holonomy estimate to expose the growing-window and growing-group rates still missing.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**ESTABLISHED EXACT-HOLONOMY NO-GO AND FIXED-TYPE TRACE
REGULARIZATION; GLOBAL ROUTE OPEN.**

Let a group `K` act on a finite set `Y`, with a Hilbert space of the same
dimension `r` over every point.  An exact block cocycle is a family

~~~text
c(g,y): V_y -> V_(gy),
c(gh,y)=c(g,hy)c(h,y).                                  (BFH1)
~~~

On each orbit, choose a root `o` and one transport from `o` to every point.
A block-diagonal gauge makes all chosen transports the identity.  The
remaining data are exactly the unitary representation

~~~text
rho_o: Stab_K(o) -> U(V_o),       rho_o(h)=c(h,o),       (BFH2)
~~~

up to conjugacy.  In particular the cocycle has a point basis, equivalently
is gauge-equivalent to a monomial cocycle, if and only if every stabilizer
holonomy representation is monomial.  This is representation data, not an
additive Hilbert-space `1`-cocycle.  Property (T) does not force it to be
trivial or monomial.

There is an exact property-(T) countermodel.  More generally, let `H` be a
finite group with an irreducible unitary representation `rho` of dimension
`s>1` such that

~~~text
min_[L proper in H] [H:L] > s^2.                        (BFH3)
~~~

Then no amplification `rho^(direct_sum k)` is monomial.  The normalized
character `chi_rho/s` has a positive distance `Delta(H,rho)>0` from the
compact polytope of normalized monomial characters.  For any finite
generating set `S` of `H` there is `a(H,rho,S)>0` such that, for every `k`,
every monomial representation `mu`, every unitary `Z`, and even after adding
`o(ks)` arbitrary padding dimensions,

~~~text
max_(s in S) ||Z(rho^(direct_sum k))(s)Z^*-mu(s)||_2
 >= a(H,rho,S)-o(1).                                    (BFH4)
~~~

One concrete choice is the binary icosahedral group
`H=SL(2,5)` with its natural irreducible two-dimensional representation:
`H` is finite and hence has property (T), while every proper subgroup has
index at least `5>2^2`.  Put this holonomy over every atom of a trivial
finite Boolean pattern action.  The lamp atoms have exactly equal,
hence canonical, trace; all actor products and lamp covariance equations are
exact; nevertheless the fiber cocycle stays uniformly far from every
atom-preserving monomial action.  The example deliberately does **not**
have the canonical actor or mixed crossed-product traces.  It proves the
sharp limitation: property (T) alone cannot remove the quantum fiber.

Canonical mixed trace does give a quantitative positive result for each
fixed finite holonomy group.  Let `H` be finite and let
`sigma:H->U(r)` be an exact representation.  Write

~~~text
c(h)=tr_r(sigma(h)),
q=sum_(h!=1)|c(h)|,
delta=q+2|H|/r.                                         (BFH5)
~~~

There are an exact monomial representation `mu:H->U(r)` and a unitary `Z`
such that, for every `h in H`,

~~~text
||Z sigma(h) Z^*-mu(h)||_2 <= 2 sqrt(delta).             (BFH6)
~~~

Indeed one may take
`mu=floor(r/|H|) lambda_H direct_sum 1^t`, where
`0<=t<|H|`.  Consequently, if `H` is fixed,
`r_n->infinity`, and `tr(sigma_n(h))->0` for every
`h!=1`, then `sigma_n` is asymptotically monomial.  This is the exact
finite-holonomy form of the canonical crossed-product mixed-trace
constraint.

For the pinned Kun--Thom wreath, after coarse Boolean block normalization,
a loop fixing an atom has conditional character

~~~text
tr(P_y U_h)/tr(P_y),                                    (BFH7)
~~~

and the canonical group trace makes this tend to zero for every fixed
nonidentity loop.  Hence a persistent obstruction cannot live in one fixed
finite exact holonomy type.  It must escape through a growing loop group,
failure of uniform exactification, or both.  The estimate makes the missing
uniformity explicit: if `|c(h)|<=epsilon` on a finite holonomy group `H`,
then

~~~text
delta <= (|H|-1)epsilon + 2|H|/r.                       (BFH8)
~~~

For an `m`-lamp canonical atom in matrix dimension `D`,
`r approximately D/2^m`.  Thus this regularization requires, at least by
the present bound,

~~~text
|H| epsilon ->0,             |H| 2^m / D ->0.           (BFH9)
~~~

By contrast, killing the fiber using lamp refinement alone requires bounded
atom rank and therefore

~~~text
m >= log_2(D)-O(1).                                     (BFH10)
~~~

Hyperlinear convergence is pointwise after each finite word and lamp window
is fixed.  It supplies neither the `ell^1` mixed-trace rate over growing
`H` in `(BFH9)` nor control at the logarithmic window in `(BFH10)`.
Property (T) supplies a spectral gap for almost invariant vectors, but no
bound on the sizes or monomiality of these exact finite-image holonomies.
Closing that two-parameter gap is still the hyperlinear-to-sofic theorem.
Nothing here proves that the pinned wreath is nonhyperlinear.

DERIVATION
fixed-holonomy-character-regularization-and-quantum-fiber-proof
