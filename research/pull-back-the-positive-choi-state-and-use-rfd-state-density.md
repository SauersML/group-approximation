---
rg: 2
id: pull-back-the-positive-choi-state-and-use-rfd-state-density
kind: route
title: Pull the Choi state through the quotient and approximate it by finite-dimensional RFD vector states
target: positive-tree-separator-has-fd-low-ideal-moment-packets
requires:
  - tree-face-separator-signedness-is-removable-modulo-the-unit
  - virtually-free-full-algebras-are-rfd
---

We first record the state-density fact used in the proof.

> If a unital C-star algebra `C` is residually finite-dimensional, then its
> finite-dimensional vector states are weak-star dense in its whole state
> space.

Let `K` be the weak-star closed convex hull of the finite-dimensional vector
states.  If a state `phi` were outside `K`, real Hahn--Banach separation would
give `a=a^* in C` with

```text
phi(a)>sup_(psi in K)psi(a).                                (1)
```

Choose `t>||a||`, so `b=a+t1` is positive.  Residual finite-dimensionality
gives

```text
||b||=sup_(rho finite-dimensional)||rho(b)||
     =sup_(rho,v)||<rho(b)v,v>||,                           (2)
```

where positivity removes the absolute value in the last supremum.  Hence the
right side of `(1)` is

```text
sup_(rho,v)<rho(a)v,v>=||a+t1||-t=max sigma(a),             (3)
```

which is the supremum over all states, contradicting `(1)`.  A finite convex
combination of finite-dimensional vector states is again one such state: use
the direct-sum representation and weight the vector components by square
roots of the convex coefficients.  Thus the convex hull may be replaced by
the set of finite-dimensional vector states itself.

Since `A=C^*(G_0)` is RFD, every matrix amplification and finite direct sum
of amplifications is RFD.  In particular `D_A` is RFD.

Now pull `omega` back to the state

```text
omega_tilde=omega o q_D                                    (4)
```

on `D_A`.  It has

```text
omega_tilde(X_tilde)=omega(X)>=c_H delta.                  (5)
```

If `y in ker q_D`, then

```text
omega_tilde(y^*y)=omega(q_D(y)^*q_D(y))=0.                 (6)
```

Use the state-density result on the finite self-adjoint test set consisting
of `X_tilde` and the positive elements `y^*y`, `y in Y`.  A sufficiently
accurate finite-dimensional vector state

```text
z |-> <Pi(z)xi,xi>
```

then satisfies `(PTF3)`, and its approximation to the zero values in `(6)`
can be chosen so that their finite sum is below `epsilon`.  Since

```text
<Pi(y^*y)xi,xi>=||Pi(y)xi||^2,
```

this is `(PTF4)`.

Finally, a representation of a summand `M_n(A)` is an amplification of a
representation of `A`; a representation of a finite direct sum decomposes
over its central summands.  Therefore `Pi,xi` are equivalently a finite
packet of finite-dimensional representations of `A` with finitely many
vector coordinates, proving the packet interpretation.

The proof only approximates finitely many state values.  It gives no uniform
operator bound on `Pi(y)`, and the augmentation summand cannot be discarded
because the tree defect can have nonzero augmentation.  These observations
give the three scope limitations in the claim.
