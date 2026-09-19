---
rg: 2
id: qutrit-head-only-finite-envelope-proof
kind: route
title: Close the scalar and head coefficients under root commutators
target: qutrit-head-only-overlap-envelope-is-finite
requires:
  - matched-leavitt-opposite-root-qutrit-bridge-is-gl28
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - binary-jacobson-constant-q-root-envelope-is-finite
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
  - finite-support-corner-localizes-obstruction
---

Split the first module coordinate along `D_27` and write `star` for the
second coordinate.  The three non-packet generators in `(QHF1)` become

```text
1+E_(0,star),       1+E_(star,0),       1+E_(0,star)(Q).
                                                               (QHF3)
```

The packet and the first two roots generate the full scalar group
`EL_28(F_2)=GL_28(F_2)` by the one-chart theorem.  Scalar permutation
conjugacy therefore moves the last root in `(QHF3)` to

```text
x_ij(Q)                    for every i!=j.               (QHF4)
```

Together with the scalar roots, root additivity and the commutator identity

```text
[x_ik(a),x_kj(b)]=x_ij(ab)
```

show that the group contains `x_ij(a)` for every `a in A_Q` and every
root position.  Hence it contains `EL_28(A_Q)`.  Conversely every
generator has entries in `A_Q` and is elementary there, proving equality.

The coefficient algebra is finite.  Since `Q^2=Q` and `Q` is neither
zero nor one, evaluation at the two idempotent values gives

```text
A_Q -> F_2 x F_2,        a+bQ |-> (a,a+b),               (QHF5)
```

an isomorphism.  Elementary groups commute with finite products, and over
`F_2` the determinant has no nontrivial unit value.  Therefore

```text
EL_28(A_Q)
  isomorphic to EL_28(F_2) x EL_28(F_2)
  = GL_28(F_2) x GL_28(F_2),                             (QHF6)
```

which is finite.  Any further `A_Q`-labelled roots were already included
in this group.

Both the proper qutrit marginal and each head root are nonzero elements of
the finite group algebra package, so its faithful left regular
representation retains them.  Arbitrary additive coefficients, rather than
only conjugacy or Morita transports, remain inside `C[H_Q]` and are exact
in that finite model.  Finite-support localization therefore cannot produce
a nonhyperlinear subgroup from this envelope.

Finally, in stable Steinberg rank the specified lifts project onto the finite
group `H_Q` and meet the Steinberg kernel centrally.  Their generated group
is central-by-finite, hence amenable and hyperlinear.  The cover supplies no
extra obstruction.
