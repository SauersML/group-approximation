---
rg: 2
id: mf-separation-balances-central-involutions-at-trace-zero
kind: claim
title: MF separation balances every central involution at trace zero
distinct_from:
  q8-bs23-terminal-mark-is-exactly-invisible-but-hyperlinear: that constructs Hilbert--Schmidt microstates for one finitely presented hyperlinear group; this proves a general operator-norm balancing theorem conditional only on MF separation of the central mark.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that finds an exact divisibility wall and a logarithmic finite-window reservoir; this shows abstractly that an MF embedding would necessarily exploit such an unbounded reservoir.
  property-t-actor-keeps-fd-invisible-center-in-lef-models: that gives explicit finite regular models using residual quotients; this extracts balanced models from arbitrary operator-norm MF approximations without a quotient model.
---

**ESTABLISHED MF NO-GO; THIS DOES NOT PROVE THE TARGET GROUPS ARE MF.**

Let Gamma be a finitely generated MF group and let

~~~text
z in Z(Gamma),          z^2=1,          z!=1.             (MFB1)
~~~

Then Gamma has finite-dimensional operator-norm almost representations
sigma_n for which

~~~text
tr(sigma_n(z)) -> 0,
||sigma_n(z)-I||_2^2 -> 2.                               (MFB2)
~~~

Here almost representation means asymptotic multiplicativity on every fixed
finite subset. If Gamma is finitely presented, the images of a fixed finite
generating set have operator-norm defects tending to zero for every relator
of that presentation.

The construction is canonical. MF separation gives unitary maps u_n with

~~~text
liminf ||u_n(z)-I|| > 0.                                 (MFB3)
~~~

Because z is a central involution, u_n(z) is close to an involution and
almost commutes in operator norm with every fixed u_n(g). Round it by
functional calculus to a self-adjoint involution and let P_n be its negative
spectral projection. Condition MFB3 makes P_n nonzero. The subspaces
P_n H_n are almost invariant. Polar decomposition of the compressed
operators produces operator-norm almost representations v_n on P_n H_n
with

~~~text
v_n(z) -> -I                                             (MFB4)
~~~

in operator norm. Take the direct sum of v_n with the same-dimensional
trivial representation. The z-word is then asymptotic to

~~~text
(-I) direct_sum I,
~~~

which proves MFB2, while taking a direct sum does not increase any
operator-norm relation defect.

If, in addition, every exact finite-dimensional representation of Gamma
kills z, the dimensions in this balanced sequence must tend to infinity.
Otherwise compactness of finitely many unitary groups would give a
bounded-dimensional exact representation in which z has both signs.

Thus an MF hypothesis cannot promote exact finite-dimensional invisibility
to asymptotic invisibility. It points in the opposite direction: MF
separation of the nontrivial group element forces an operator-norm
ultraproduct loophole, and centrality lets one make its trace macroscopic.
The theorem applies if either C^*(Gamma) or C_r^*(Gamma) is MF, since either
embedding makes Gamma an MF group.

This statement does not establish MF for the Q8/BS(2,3) terminal group or
for the shared-center property-(T) group. It only gives the exact
conditional consequence and prevents MF from being invoked as a collapse
mechanism. LLP is not addressed. No nonhyperlinear group is constructed.

DERIVATION
negative-mf-corner-plus-trivial-copy-balances-mark-proof
