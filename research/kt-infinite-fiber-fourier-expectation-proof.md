---
rg: 2
id: kt-infinite-fiber-fourier-expectation-proof
kind: proof
title: Fourier expectation kills supported transport across an infinite KT coefficient fiber
proves:
  - kt-canonical-lamp-collision-forces-vanishing-intertwiner
requires:
  - finite-abelian-hs-almost-actions-round-in-the-same-dimension
  - intermediate-ring-truncations-preserve-the-kt-named-return-proof
---

# Fourier expectation kills supported transport across an infinite KT coefficient fiber

## 1. A finite collision theorem

Let `A` and `B` be label sets, let `f:A->B`, and choose distinct
labels

~~~text
a_0,a_1,...,a_r in A,        f(a_0)=...=f(a_r)=b.          (1)
~~~

In a tracial matrix algebra `M_d`, let

~~~text
z_0,...,z_r,w
~~~

be commuting self-adjoint involutions. Think of `z_j` as the source lamp
at `a_j` and `w` as the target lamp at `b`. Let `T` be a partial
isometry, put `P=T^*T`, and write

~~~text
q=tau(P)=||T||_2^2,
delta=max_(0<=j<=r)||wT-Tz_j||_2.                          (2)
~~~

For `1<=j<=r` set

~~~text
h_j=z_0z_j.
~~~

The collision covariance gives

~~~text
||Th_j-T||_2
 <=||Tz_0-wT||_2+||Tz_j-wT||_2
 <=2delta.                                                 (3)
~~~

The involutions `h_j` commute and generate an elementary abelian group
of rank `r`. Its invariant projection is

~~~text
E=2^(-r) product_(j=1)^r(I+h_j)
 =2^(-r) sum_(S subset {1,...,r}) product_(j in S)h_j.     (4)
~~~

Telescope (3) along each product in (4) and average. Each index occurs in
half of the subsets, so

~~~text
||T-TE||_2<=r delta.                                       (5)
~~~

The two terms `TE` and `T(I-E)` are Hilbert--Schmidt orthogonal.
Moreover,

~~~text
||TE||_2^2=tau(EPE)<=tau(E).
~~~

Therefore

~~~text
q<=tau(E)+r^2 delta^2.                                     (6)
~~~

Suppose the lamp character is `epsilon`-canonical on the collision
subgroup:

~~~text
|tau(product_(j in S)h_j)|<=epsilon
          for every nonempty S.                            (7)
~~~

Expanding (4) in (6) gives the sharp finite-fiber estimate

~~~text
q<=2^(-r)+(1-2^(-r))epsilon+r^2 delta^2.                   (8)
~~~

For `r=1` this is the representation-theoretic version of the named
fiber pairing: a trace-zero collision lamp caps an exact supported
transport at one half of physical trace.

The factor `2^(-r)` is sharp. In a regular-multiple representation of
the finite lamp group, choose a unitary `U` with `wU=Uz_0` and let
`T=UE`. Then `wT=Tz_j` for every `j` and `T^*T=E` has trace
`2^(-r)`.

## 2. Passage from arbitrary canonical microstates

Let `phi_n` be any canonical normalized-Hilbert--Schmidt microstate
sequence of a generalized binary wreath. For every fixed finite lamp
packet, the matrices assigned to its lamp subgroup form an asymptotic
representation of a fixed finite elementary abelian group. By
`finite-abelian-hs-almost-actions-round-in-the-same-dimension`, they may
be perturbed by `o_2(1)`, in the same matrix dimension, to commuting
self-adjoint involutions.

Canonical trace is preserved under this perturbation. Products of distinct
lamp generators are nonidentity group elements, so their normalized traces
tend to zero. Thus, for every fixed collision packet (1), the rounded
matrices satisfy

~~~text
epsilon_n->0.                                              (9)
~~~

Any covariance errors in (2) change by only `o(1)` under the same
rounding. Consequently (8) applies to arbitrary canonical microstates,
not only to regular, congruence, permutation, or truncated-cone models.

In particular, if `f` has arbitrarily large finite fibers and a sequence
of partial isometries `T_n` satisfies the covariance in (2) for every
fixed source label, then for every fixed `r`,

~~~text
limsup_n tau(T_n^*T_n)<=2^(-r).                            (10)
~~~

Letting `r` tend to infinity after taking the limsup gives

~~~text
tau(T_n^*T_n)->0.                                         (11)
~~~

Only pointwise canonical trace is used: `r` is fixed while
`n->infinity`. No uniform trace bound over a growing lamp group and no
multiplicity assumption is inserted.

## 3. The infinite KT coefficient fiber

Use

~~~text
S=F_2[x_1,y,x_3],
P=F_2[x_1,x_1y,x_3],
V=S/P
~~~

as vector spaces, and let

~~~text
X:V->V,                  X[f]=[x_1f].                      (12)
~~~

The map is well defined because `x_1P subset P`. Its kernel contains the
linearly independent vectors

~~~text
eta_(b,c)=[x_1^(b-1)y^b x_3^c],
                         b>=1, c>=0,                       (13)
~~~

since multiplication by `x_1` changes the exponent inequality from
`b-1<b` to `b=b`. In fact these monomials form a basis of `ker X`,
but only infinite independence is needed. The named direction is

~~~text
eta_(1,0)=[y].                                             (14)
~~~

The root-coset injection

~~~text
V -> H/Gamma,          [g] |-> e_12(g)Gamma                (15)
~~~

turns the vectors in (13) into distinct lamp sites of the coherent
intermediate Kun--Thom wreath. All of them lie in the single fiber
`X^(-1)(0)`.

Let `z_[g],n` denote their lamp matrices in an arbitrary canonical
microstate sequence. Suppose a proposed coefficient transport supplies
partial isometries `T_n` and target lamps `w_[Xg],n` such that, for
every fixed `[g] in V`,

~~~text
||w_[Xg],n T_n-T_n z_[g],n||_2 ->0.                       (16)
~~~

Apply (10) to any `r+1` distinct vectors from (13). Since `r` is
arbitrary, (11) gives

~~~text
tau(T_n^*T_n)->0.                                         (17)
~~~

Already the pair `0,[y]` gives the half-trace cap. The rest of the fixed
kernel basis drives the supported trace all the way to zero.

## 4. Exact scope

Equation (17) is the desired extension of the fiber-pairing obstruction:
it holds in arbitrary canonical-trace finite-dimensional microstates and
is insensitive to representation multiplicity. The regular additive
carrier from the cone calculation is one realization, not a hypothesis.

The theorem is conditional on the existence of one supported transport
`T_n` satisfying all fixed covariance rows (16). Canonical trace by itself
does not manufacture such a transport from the actor matrices. Indeed the
sharp examples following (8) realize every finite collision packet on
support exactly `2^(-r)`; a sequence can keep solving larger packets by
letting that support vanish.

Therefore this closes a positive-density noncongruence escape: no
partial-isometry implementation of the noninjective coefficient map can
retain named physical weight. It does not close the global
actor-exactification problem, whose missing step is precisely to force a
large-support transport from the full KT actor and compressor relations.
The nonhyperlinearity root remains open.
