---
rg: 2
id: kt-canonical-lamp-collision-forces-vanishing-intertwiner
kind: claim
title: Canonical KT lamp traces force every infinite-fiber transport to vanish
artifacts:
  - research/kt-infinite-fiber-fourier-expectation-proof.md
distinct_from:
  kt-no-denominator-window-balances-coefficient-and-canonical-inverse: That computes the defect on the regular additive carrier of each finite cone truncation; this is representation-theoretic and applies to arbitrary canonical-trace matrix microstates.
  kt-tensor-mask-isometry-and-positive-density-multiplicity-proof: That shows regular trace masks leave arbitrary multiplicity fibers invisible; this proves multiplicity cannot protect a positive-trace partial transport across infinitely many canonical lamp collisions.
  finite-abelian-hs-almost-actions-round-in-the-same-dimension: That rounds one finite abelian packet; this combines those fixed-packet roundings with an infinite-fiber conditional expectation and takes the packet rank to infinity only after the microstate limit.
---

**ESTABLISHED CONDITIONAL TRANSPORT NO-GO; THE GLOBAL ROOT REMAINS OPEN.**

Let `f:A->B` have a fiber containing distinct labels
`a_0,...,a_r`. In a tracial matrix algebra, let `z_j` be the commuting
source-lamp involutions, let `w` be the target lamp at their common image,
and let `T` be a partial isometry. Put

~~~text
q=tau(T^*T),
delta=max_j ||wT-Tz_j||_2.
~~~

If every nontrivial product of the collision involutions
`h_j=z_0z_j` has normalized trace at most `epsilon`, then

~~~text
q<=2^(-r)+(1-2^(-r))epsilon+r^2 delta^2.                  (CLF1)
~~~

The proof is the finite Fourier expectation

~~~text
E=2^(-r) product_(j=1)^r(I+h_j).
~~~

Collision covariance gives `||T-TE||_2<=r delta`, while
`||TE||_2^2<=tau(E)`. The coefficient `2^(-r)` is sharp.

Now take any canonical normalized-Hilbert--Schmidt microstate sequence of a
binary generalized wreath. Each fixed finite lamp packet rounds in the same
dimension to commuting involutions, and canonical trace makes every
nontrivial fixed lamp product have trace tending to zero. Therefore (CLF1)
holds asymptotically for arbitrary canonical microstates, with no congruence,
regularity, permutation, or multiplicity hypothesis.

For the coherent intermediate Kun--Thom actor, put

~~~text
S=F_2[x_1,y,x_3],
P=F_2[x_1,x_1y,x_3],
V=S/P,
X[f]=[x_1f].
~~~

The fiber `X^(-1)(0)` contains the infinite independent family

~~~text
eta_(b,c)=[x_1^(b-1)y^b x_3^c],       b>=1, c>=0,         (CLF2)
~~~

whose first member is the named vector `eta_(1,0)=[y]`. Through the
root-coset injection `V->H/Gamma` these are distinct lamp sites.

Consequently, if partial isometries `T_n` in an arbitrary canonical
microstate sequence implement the coefficient transport on every fixed
site,

~~~text
||w_[Xg],n T_n-T_n z_[g],n||_2 ->0
                   for every fixed [g] in V,               (CLF3)
~~~

then

~~~text
tau(T_n^*T_n)->0.                                          (CLF4)
~~~

Indeed (CLF1) first gives the named half-trace cap from `0,[y]`, then the
rank-`r` cap `2^(-r)` from any fixed `r` kernel directions, and finally
(CLF4) by taking `r->infinity` after the microstate limit.

Thus the eta fiber-pairing obstruction does extend beyond cone and
congruence models: canonical trace alone forbids a **positive-physical-trace
implementation** of the noninjective coefficient map, even inside arbitrary
multiplicity blocks. The precise remaining escape is not a hidden
noncongruence transport; it is the absence of any theorem forcing actor
microstates to supply a large-support transport satisfying (CLF3). Finite
collision packets attain the bound by shrinking support to `2^(-r)`.
Closing that actor-to-transport step remains the nonhyperlinearity seam.

DERIVATION
kt-infinite-fiber-fourier-expectation-proof
