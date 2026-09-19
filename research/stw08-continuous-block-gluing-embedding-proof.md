---
rg: 2
id: stw08-continuous-block-gluing-embedding-proof
kind: route
title: Cover each base by the Cantor set and use the finite coordinate embedding
target: stw08-continuous-block-gluings-preserve-af-embeddability
requires: []
---

Fix `j`.  If `X_j` is compact, put `X_j^+=X_j`; otherwise let `X_j^+` be its
one-point compactification.  This convention makes `C_0(X_j)` the whole of
`C(X_j^+)` in the compact case and the ideal vanishing at infinity in the
noncompact case.  The space `X_j^+` is compact metrizable.  Choose a
continuous surjection

```text
q_j:K_j->X_j^+
```

from the Cantor set.  Pullback along `q_j` embeds `C(X_j^+)` into
`C(K_j)`, hence embeds its ideal `C_0(X_j)`.  If
`eta_j:A_j->E_j` is an AF embedding, injectivity of the minimal tensor
product gives

```text
C_0(X_j,A_j)=C_0(X_j) tensor_min A_j
  -> C(K_j) tensor_min E_j.                           (2)
```

The target in (2) is AF: `C(K_j)` is AF because the Cantor set is
zero-dimensional, and minimal tensor products of AF algebras are AF.
Taking the finite direct sum of (2) embeds the ambient algebra in (1) into
the AF algebra

```text
E=direct_sum_j (C(K_j) tensor_min E_j).
```

Restriction to `P` remains injective.  This proves the first assertion.

A pullback is, by definition, a C*-subalgebra of the direct sum of its two
coordinates.  Iterating the coordinate maps embeds every finite pullback
tree into the direct sum of its leaf blocks, so the pullback conclusion
follows without surjectivity.  A mapping torus is the pullback subalgebra of

```text
A direct_sum C([0,1],B)
```

cut out by its two endpoint equations.  Finite recursive subhomogeneous
algebras are finite iterated pullbacks of blocks `C(X,F)` with `F`
finite-dimensional.  These are the stated specializations.

For the trace assertion, use compactness to choose the Cantor surjection
directly onto `X_j`, so that (2) is unital.  The state on the unital
subalgebra

```text
q_j^*(C(X_j^+)) subseteq C(K_j)
```

defined by `mu_j` extends to a state on `C(K_j)`; write `nu_j` for its
representing probability measure.  Equivalently, `(q_j)_* nu_j=mu_j`.
Therefore the tracial state

```text
nu_j tensor sigma_j
```

on `C(K_j) tensor E_j` restricts along (2) to the product trace
`mu_j tensor tau_j`.  The weighted direct-sum trace
`sum_j lambda_j(nu_j tensor sigma_j)` on `E` consequently restricts to
`Theta` on `P`.

The product trace `mu_j tensor tau_j` is faithful on `C(X_j,A_j)`: a
nonzero positive continuous function is detected by faithful `tau_j` on a
nonempty open set, and full support of `mu_j` gives that set positive
measure.  Positive weights then make `Theta` faithful on `P`, because the
coordinate map in (1) is injective.  Since `P` contains the ambient unit and
all embeddings in this paragraph are unital, `Theta` and its extension are
states.  Finally, a trace which extends across an AF embedding is
quasidiagonal: finite-dimensional stages of the AF target give
asymptotically multiplicative trace models after restriction to `P`.

**Trust boundary.**  The construction uses only the Cantor-surjection theorem
for compact metrizable spaces, injectivity of minimal tensoring, elementary
AF permanence under tensor products and finite sums, positive state extension
on a commutative C*-algebra, and coordinate injectivity.  It does not use a
UCT or classification theorem and makes no assertion for infinite products
or infinite pullback trees.
