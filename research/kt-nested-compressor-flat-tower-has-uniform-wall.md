---
rg: 2
id: kt-nested-compressor-flat-tower-has-uniform-wall
kind: claim
title: A nested Kun--Thom compressor flat tower carries a uniform one-edge wall
distinct_from:
  one-compressor-covariance-has-free-hs-telescope: That copies an arbitrary coefficient representation along one interval and estimates the covariance boundary, but it does not produce a relative-commutant wall; this chooses a separating quotient at every depth and puts a macroscopic wall on essentially every interior level.
  polynomial-compressor-has-explicit-finite-quotient-wall: That gives one fixed finite quotient wall whose contribution is canonical-profile null; this uses quotients of increasing nilpotence depth and spreads their successive walls over a flat tower with asymptotically full density.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: That obtains a wall indirectly from canonical sofic models of the whole one-compressor wreath; this gives the coefficient modules, block shifts, covariance error, and marked fold gap explicitly.
  amenable-multi-compressors-have-a-joint-hs-telescope: That copies coefficient data over Folner sets for an amenable compression monoid and proves simultaneous local covariance; this treats one nested chain and additionally inserts a commutant gauge which remains macroscopically visible after return.
  homogeneous-quotient-near-genuine-microstates-are-deep: That concerns arithmetic conductor profiles in homogeneous-quotient crossed products; this is a polynomial Kun--Thom quotient tower and a direct relative-wall construction.
  bare-relative-wall-exists: That asks for the wall in a Connes-embeddable representation of the full Kun--Thom actor G; this constructs it only for the one-compressor ascending-HNN subgroup and proves that extending it to G cannot be a boundary-only exact-block repair.
---

**ESTABLISHED, WITH THE FULL-ACTOR SCOPE EXPLICIT.**  Let

```text
P=F_q[x,y,z_3,...,z_d],       Gamma=EL_r(P),
alpha(x)=x,                   alpha(y)=xy,
alpha(z_i)=z_i,               r,d>=3,                         (KFT1)
```

and let

```text
V=<Gamma,t | t delta t^(-1)=alpha(delta), delta in Gamma>
```

be the one-compressor ascending HNN subgroup of the Kun--Thom actor.  Fix a
root pair `(a,b)` and put `gamma=e_(ab)(y)` and
`h=t^(-1) gamma t`.

For every `L>=2` there are one finite-dimensional exact representation

```text
Pi_L:Gamma->U(K_L)
```

and two unitaries `T_(0,L),T_(1,L)` such that

```text
max_(epsilon=0,1)
 ||T_(epsilon,L) Pi_L(delta) T_(epsilon,L)^*
                 -Pi_L(alpha(delta))||_2 <= 2/sqrt(L)       (KFT2)
```

for every `delta in Gamma`, while

```text
||T_(0,L)^* Pi_L(gamma) T_(0,L)
       -T_(1,L)^* Pi_L(gamma) T_(1,L)||_2^2
       >= 2(1-1/L).                                        (KFT3)
```

Thus the two generator maps agree **exactly** on `Gamma`, their fixed
ascending-HNN relators tend to zero in normalized Hilbert--Schmidt norm, and
the returned element `h` has a uniform fold gap.  Passing to a tracial matrix
ultraproduct gives a bare relative wall for `Gamma<V`.

The construction does **not** extend the wall to the full Kun--Thom actor
`G`.  There is, however, a sharp exact-block firewall.  Suppose a
tower-preserving attempted full-`G` extension decomposes as an orthogonal
sum of blocks, and on a subspace of normalized dimension `1-beta_L` its two
vertex maps are genuine representations of `G` agreeing on `Gamma`.  If its
squared `h`-fold gap is `c_L`, then

```text
beta_L >= c_L/4.                                           (KFT4)
```

In particular, retaining `(KFT3)` requires
`beta_L>=1/2-o(1)`.  An `o(L)` collection of exceptional levels, a
vanishing-density wrap correction, or a bounded-dimensional holonomy cannot
extend this flat tower to the full actor.  Any successful full-`G` extension
must be genuinely non-exact/nonliftable on positive density, or must mix the
level decomposition so thoroughly that the flat-tower block structure is
lost.  Constructing that extension is exactly the still-open full-actor
bare-wall seam; it is not supplied here.

Proof: `kt-nested-compressor-flat-tower-wall-proof`.
