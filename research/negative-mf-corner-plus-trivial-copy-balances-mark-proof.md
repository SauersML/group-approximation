---
rg: 2
id: negative-mf-corner-plus-trivial-copy-balances-mark-proof
kind: route
title: Compress an MF model to its negative central corner and balance it
target: mf-separation-balances-central-involutions-at-trace-zero
requires:
  - exact-fd-invisibility-has-no-general-hs-robustification
---

# Compress an MF model to its negative central corner and balance it

All operator norms below are unnormalized and all traces and
Hilbert--Schmidt norms are normalized.

## 1. Start from an MF embedding

Use the group-theoretic definition of MF: Gamma embeds in the unitary group
of a norm matrix ultraproduct. Choose unitary lifts and diagonalize over
finite subsets. This gives maps

~~~text
u_n:Gamma -> U(d_n),              u_n(1)=I,              (1)
~~~

such that, for every fixed g,h in Gamma,

~~~text
||u_n(gh)-u_n(g)u_n(h)|| -> 0,                           (2)
~~~

and, for every fixed g!=1,

~~~text
liminf_n ||u_n(g)-I|| > 0.                              (3)
~~~

Only (3) for g=z will be used.

Put Z_n=u_n(z). From z^2=1 and (2),

~~~text
||Z_n^2-I|| -> 0.                                       (4)
~~~

Since z is central, zg=gz. Applying (2) twice gives, for each fixed g,

~~~text
||[Z_n,u_n(g)]|| -> 0.                                  (5)
~~~

## 2. Round the central mark and keep its negative space

A unitary Z satisfying ||Z^2-I||<=delta has spectrum in shrinking
neighborhoods of {1,-1}. For all sufficiently small delta those
neighborhoods are disjoint. Functional calculus then defines the nearest
self-adjoint involution

~~~text
Zhat_n=1 on the component near 1,
Zhat_n=-1 on the component near -1,                      (6)
~~~

and

~~~text
||Z_n-Zhat_n|| -> 0.                                    (7)
~~~

Set

~~~text
P_n=(I-Zhat_n)/2.                                        (8)
~~~

The projection P_n is nonzero for all sufficiently large n. Otherwise
Zhat_n=I along a subsequence, and (7) would contradict the MF separation
(3) for z.

Equations (5) and (7) imply

~~~text
||[P_n,u_n(g)]|| -> 0                                   (9)
~~~

for each fixed g. Thus the nonzero spaces K_n=P_n C^(d_n) are almost
invariant in operator norm, not merely in normalized Hilbert--Schmidt norm.

## 3. Polar-compress the whole finite window

On K_n define the compression

~~~text
C_n(g)=P_n u_n(g) P_n restricted_to K_n.                (10)
~~~

For a unitary U and a projection P,

~~~text
(PUP)^*(PUP)
 =P-P U^*(I-P)U P.                                      (11)
~~~

The norm of the last term is at most ||[P,U]||^2. Hence (9) makes C_n(g)
invertible on K_n for every fixed g and all sufficiently large n. Let

~~~text
v_n(g)=polar(C_n(g)) in U(K_n).                          (12)
~~~

Continuous functional calculus in (11) gives

~~~text
||v_n(g)-C_n(g)|| -> 0.                                 (13)
~~~

For fixed g,h, insert P_n between the compressed factors. The error in
removing that middle projection is bounded by one of the commutators in
(9); the error in replacing u_n(g)u_n(h) by u_n(gh) is controlled by (2).
Using (13) on the three fixed elements gives

~~~text
||v_n(gh)-v_n(g)v_n(h)|| -> 0.                          (14)
~~~

Thus v_n is again an operator-norm almost representation on every fixed
finite set.

On K_n, the rounded involution is exactly -I. Equations (7), (10), and
(13) therefore give

~~~text
||v_n(z)+I_(K_n)|| -> 0.                                (15)
~~~

## 4. Balance with a trivial copy

Let r_n=dim(K_n)>=1 and define

~~~text
sigma_n(g)=v_n(g) direct_sum I_(r_n) in U(2r_n).         (16)
~~~

The second summand is the exact trivial representation, so (14) remains
true for sigma_n with exactly the same maximum defect. From (15),

~~~text
sigma_n(z) -> (-I_(r_n)) direct_sum I_(r_n)              (17)
~~~

in operator norm. Consequently

~~~text
tr(sigma_n(z)) -> 0,
||sigma_n(z)-I||_2^2
 =2-2 Re tr(sigma_n(z))
 ->2.                                                     (18)
~~~

If a finite presentation is fixed, apply (14) successively along each
relator word. Its operator-norm defect tends to zero, and (18) holds for
the word representing z.

## 5. Exact invisibility forces unbounded balanced dimension

Suppose every exact finite-dimensional representation of Gamma kills z.
If 2r_n were bounded along a subsequence, pass to one on which r_n is
constant. For a fixed finite generating set, compactness of the
corresponding finite product of unitary groups gives a convergent
subsequence of the tuples sigma_n. Every fixed relation holds in the
limit by (14), so the limiting tuple defines an exact finite-dimensional
representation of Gamma. Equation (17) makes the image of z have a
nonzero negative eigenspace, a contradiction.

Therefore

~~~text
r_n -> infinity                                         (19)
~~~

after discarding finitely many terms. The unbounded multiplicity/window
reservoir is not an artifact of the shared-center construction; it is
forced abstractly whenever MF separation coexists with exact
finite-dimensional invisibility.

The theorem is conditional on Gamma being MF. It neither proves MF for
the current terminal candidates nor supplies LLP. Its role is a sharp
logical fence: MF cannot be the hypothesis that collapses the invisible
central mark, because MF separation plus centrality manufactures balanced
operator-norm countermodels.
