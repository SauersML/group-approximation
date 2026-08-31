---
rg: 2
id: regular-packet-central-sector-multiplicity-proof
kind: route
title: Decompose the regular central sector and expose its Fourier reservoir
target: canonical-regular-packets-leave-an-unbounded-cartan-reservoir
requires:
  - fixed-extraspecial-packet-is-morita-neutral-for-code-rounding
  - irreducible-finite-packet-normalizer-words-scalarize
  - collision-and-phase-free-cartan-observables-force-joint-lamp-targets
---

## Step 1: canonical trace fixes the Plancherel multiplicity

Let `K` be finite.  For `nu in Irr(K)` write `s=dim(nu)` and

~~~text
e_nu=(s/|K|) sum_(k in K) conjugate(chi_nu(k)) k.
                                                                    (RPM1)
~~~

The finite Peter--Weyl decomposition is

~~~text
ell^2(K) = direct_sum_(mu in Irr(K)) V_mu tensor C^(dim(mu)),
lambda_K(C[K])
 =direct_sum_mu M_(dim(mu)) tensor I_(dim(mu)).          (RPM2)
~~~

Consequently, for `pi_r=r lambda_K`,

~~~text
e_nu H_r = V_nu tensor C^s tensor C^r,
pi_r(C[K])e_nu = M_s tensor I_(sr).                      (RPM3)
~~~

The central corner has ordinary rank `r s^2` inside dimension `r|K|`.
Equivalently,

~~~text
tau_(r|K|)(pi_r(e_nu))=s^2/|K|.                          (RPM4)
~~~

Its relative commutant on the corner is `I_s tensor M_(sr)`.  This is
not an accidental choice of model.  If an exact representation `pi` has
normalized character equal to the canonical trace on `K`, character
orthogonality gives

~~~text
multiplicity_pi(nu)
 =(1/|K|) sum_k Tr(pi(k)) conjugate(chi_nu(k))
 =(dim(H)/|K|)s.                                        (RPM5)
~~~

Thus `dim(H)` is a multiple of `|K|` and `pi` is a multiple of the
regular representation.  Approximate canonical characters have the same
multiplicity proportions up to the corresponding finite character error;
the exact family already suffices for the no-go.

## Step 2: even an ideal right packet leaves external amplification

On one regular copy, refine `(RPM2)` as

~~~text
e_nu ell^2(K) = V_nu tensor V_nu^*.
~~~

The left algebra is `M_s tensor I_s` and the actual right regular algebra
is `I_s tensor M_s`, with an irrelevant opposite-algebra convention.
Together they generate `M_(s^2)` on this block.  On `r` regular copies,

~~~text
Alg(lambda_K(C[K]),rho_K(C[K]))e_nu
   =M_(s^2) tensor I_r,                                 (RPM6)
commutant =I_(s^2) tensor M_r.
~~~

So a true left/right pair removes the intrinsic factor `s` in the
left-regular multiplicity, but not the arbitrary amplification `r`.

There is also a group-theoretic warning.  A second commuting copy included as
ordinary group generators with canonical trace acts left regularly on the
second coordinate; it is not automatically `rho_K` on the first coordinate.
For `K times L` and an irreducible `nu tensor mu` of dimension `st`,
Step 1 gives

~~~text
M_(st) tensor I_(rst)                                   (RPM7)
~~~

on `r` copies of the regular representation.  Thus ordinary paired packets
retain the full Plancherel multiplicity.  Requiring the special left/right
correspondence is extra operator-algebraic data, and even that stronger datum
only reaches `(RPM6)`.

## Step 3: the qutrit central-character candidate

Let

~~~text
H_3=<x,y,z | x^3=y^3=z^3=1, z central, [x,y]=z>.
~~~

It has order `27`.  For either nontrivial character `chi(z)=omega` of its
center there is a unique irreducible representation with that central
character, of dimension `3`.  The central-character projection is

~~~text
e_chi=(1/3) sum_(a=0)^2 conjugate(chi(z^a)) z^a.         (RPM8)
~~~

It is the primitive central idempotent of that irreducible.  Equations
`(RPM3)--(RPM4)` give, on `r lambda_(H_3)`,

~~~text
tau(e_chi)=1/3,
pi(C[H_3])e_chi=M_3 tensor I_(3r).                       (RPM9)
~~~

If the genuine operator-level right copy is also supplied, `(RPM6)` gives

~~~text
M_9 tensor I_r.                                         (RPM10)
~~~

Thus the most favorable qutrit sector has a full finite matrix factor, but
its commutant is still `M_(3r)` in the group-algebra construction and
`M_r` even in the ideal paired construction.  Higher extraspecial groups and
tensor products merely replace the fixed first-factor size; they do not
remove `r`.

## Step 4: covariance factors through the reservoir

Let `A=M_S tensor I_m subset M_(Sm)` and suppose `U A U^*=A`.
Every automorphism of `M_S` is inner.  Choose `C_alpha in U(S)`
implementing the induced automorphism.  Then

~~~text
(C_alpha^* tensor I_m)U in A'=I_S tensor M_m,
~~~

so for some `W in U(m)`,

~~~text
U=C_alpha tensor W.                                    (RPM11)
~~~

Changing `C_alpha` by a scalar changes `W` by the reciprocal scalar and is
the only ambiguity.  For a family `U_g`, multiplication gives

~~~text
C_g C_h=c(g,h) C_(gh),
W_g W_h=conjugate(c(g,h)) W_(gh).                       (RPM12)
~~~

All non-scalar actor freedom therefore survives as a projective
representation on the multiplicity space.  This is precisely the
scalarization in
`irreducible-finite-packet-normalizer-words-scalarize`, now combined with
the canonical-trace calculation showing that the multiplicity is unbounded.

For product masas `D_S tensor D_m`, collision moments factor:

~~~text
Col_(D_S tensor D_m)(C tensor W)
 =Col_(D_S)(C) Col_(D_m)(W).                            (RPM13)
~~~

In particular a monomial finite implementer has collision one and transfers
the entire collision problem unchanged to `W`.  The packet can make the
finite factor canonical, but it supplies no basis on the reservoir.

## Step 5: no equivariant rank-one selector exists

The preceding freedom rules out a canonical selector without choosing a
particular actor gauge.  Let `T` be any finite tuple generating
`A=M_S tensor I_m`.  The pointwise conjugation stabilizer of `T` contains

~~~text
G_m={I_S tensor V: V in U(m)}.                          (RPM14)
~~~

Suppose a rule depending only on the unitary-conjugacy class of `T` assigned
a rank-one masa `D(T)` equivariantly.  Since every element of `G_m` fixes
`T`, it normalizes `D(T)`.  Conjugation therefore gives a continuous map
from the connected group `U(m)` to the finite permutation group of the
minimal projections of `D(T)`.  The map is constant.  Every minimal
projection `p` of `D(T)` is fixed by `G_m` and hence

~~~text
p in (I_S tensor M_m)'=M_S tensor I_m.                  (RPM15)
~~~

Every nonzero projection in the algebra on the right has rank divisible by
`m`.  For `m>1` this contradicts `rank(p)=1`.

The same proof applies after adjoining finite-sector actor implementers
`C_g tensor I_m`, or after replacing `S` by the paired size `s^2`.
Actor-dependent observables can break `G_m`, but then the needed basis comes
from the growing actor family rather than from the fixed packet.

## Step 6: an exact canonical-trace Fourier escape

Let `q=|K|` and let `F_r` be the unitary discrete Fourier matrix

~~~text
(F_r)_(a,b)=r^(-1/2) exp(2 pi i ab/r),      0<=a,b<r.
~~~

It satisfies `F_r^2 delta_b=delta_(-b)` and hence `F_r^4=I`.  Define an
exact representation of `K times C_4` on
`ell^2(K) tensor C^r` by

~~~text
Pi_r(k,t^a)=lambda_K(k) tensor F_r^a.                    (RPM16)
~~~

If `k!=1`, the trace of `lambda_K(k)` is zero.  If `k=1` and
`a=1` or `3`, the elementary quadratic Gauss bound gives

~~~text
|Tr(F_r^a)|<=sqrt(2).
~~~

For `a=2`, `F_r^2` is inversion and has at most two fixed points.  Therefore

~~~text
tau(Pi_r(k,t^a))->0 for every (k,t^a)!=(1,1).            (RPM17)
~~~

The representation has the canonical limiting group trace, while all packet
relations and the trivial actor covariance are exact.

Use the tensor basis consisting of group points and Fourier coordinates.
For `U_r=I_q tensor F_r`, direct calculation gives

~~~text
Col_D(U_r)
 =(qr)^(-1) sum_(i,j)|(U_r)_(i,j)|^4
 =1/r.                                                   (RPM18)
~~~

If `M` is monomial, it selects at most one entry in each column.  Every
nonzero entry of an old column has modulus `1/sqrt(r)`, whence

~~~text
|tau(M^*U_r)|<=1/sqrt(r),
||U_r-M||_2^2>=2-2/sqrt(r).                              (RPM19)
~~~

This is stable under sublinear padding.  If `p_r=o(qr)` and
`V_r=U_r direct_sum I_(p_r)`, then every monomial `N_r` satisfies

~~~text
|Tr(N_r^* V_r)|<=q sqrt(r)+p_r,
||V_r-N_r||_2^2
 >=2-2(q sqrt(r)+p_r)/(qr+p_r) ->2.                      (RPM20)
~~~

Thus exact finite-packet covariance and canonical group trace permit a common
reservoir unitary whose collision tends to zero and whose normalized
Hilbert--Schmidt distance from every monomial tends to `sqrt(2)`, even after
arbitrary sublinear padding.

## Step 7: exact boundary for the Kun--Thom route

The finite packet does yield a canonical coarse factor.  Minimal projections
of a masa in `M_S tensor I_m` have rank `m`, and the finite-sector part of
actor covariance permutes them rigidly.  What the packet cannot do is refine
those coarse atoms to rank one or control the reservoir factors `W_g`
simultaneously over growing windows.

Accordingly the result is a no-go for the proposed basis rigidifier, not a
counterexample to target existence.  A separate actor-dependent Cartan might
still exist.  Producing it with collision tending to one and phase-free mass
tending to zero is exactly
`collision-and-phase-free-cartan-observables-force-joint-lamp-targets`.
No nonhyperlinear group is proved here, and the global route remains OPEN.
