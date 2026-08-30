---
rg: 2
id: spherical-root-graph-character-proof
kind: route
title: Identify the graph normal closure and the moving-character phase collision
target: spherical-root-type-selection-is-phase-unsafe
requires: []
---

Let

```text
C_chi={(chi(k)^(-1),k):k in K} <= B x H,
N=normalClosure_(B x H)(C_chi),
L=normalClosure_H(K).
```

Projection to `H` maps `N` onto `L`.  If `N intersect B={1}`, this projection
is an isomorphism `N -> L`.  Hence `N` is the inverse graph of a unique map
`chi_tilde:L -> B`.  The subgroup law makes `chi_tilde` a homomorphism, the
generators show that it extends `chi`, and normality of `N` makes it invariant
under conjugation by `H`.

Conversely, suppose such an invariant extension exists.  Its inverse graph

```text
Gamma={(chi_tilde(l)^(-1),l):l in L}
```

is normal in `B x H` and contains `C_chi`, so `N <= Gamma`.  Every element of
`L` is a product of `H`-conjugates of elements of `K` and their inverses.
Invariance of `chi_tilde` says that the inverse-graph lift of such a product is
the corresponding product of conjugates of elements of `C_chi`.  Thus
`Gamma <= N`.  Therefore `N=Gamma` and `N intersect B={1}`, proving the exact
criterion.

Now suppose `B` has a fixed faithful scalar character `iota:B -> T` and
`L=H`.  In the phase-safe case define

```text
pi(b,h)=iota(b chi_tilde(h)).
```

This is a one-dimensional unitary representation of `B x H`, faithful on the
prescribed phase group, and it sends every element of `C_chi` to `1`.  If no
invariant extension exists, the criterion instead gives a nontrivial element
of `N intersect B`, so normal closure destroys phase faithfulness.  This is
the claimed dichotomy.

There is a separate vector-state fact which must not be confused with those
operator relations.  For finite `H`, take the induced `H`-module whose
distinguished coset line has character `k |-> iota(chi(k))`, and let `B` act
by `iota`.  Every graph word fixes the distinguished coset vector, regardless
of whether `K` normally generates `H`; the graph words need not be identity
operators on the rest of the induced module.  Hence a finite spherical root
always has a finite monomial vector-state model and cannot alone furnish the
required finite-dimensional soundness.

For the explicit packet, let `R` be nonempty,

```text
D=(C_2)^R,
H_R=D semidirect Sym(R),
K_R=D semidirect Stab(r_0),
chi_R(d,sigma)=d(r_0).
```

The distinguished coordinate line in the signed-permutation module has
`K_R`-character `chi_R`.  Frobenius reciprocity gives a nonzero map from the
induced module to the signed-permutation module, and both dimensions are
`|R|`.  The coordinate lamps have distinct weights and `Sym(R)` acts
transitively on them, so the signed-permutation module is irreducible.  The
map is therefore an isomorphism and the spherical vector selects exactly the
desired answer type.

Assume `|R|>=2` and choose `s!=r_0`.  Since `D<=K_R`, the graph clauses
contain

```text
(1,l_s),                              (-1,l_(r_0)).
```

A permutation conjugates the first element to `(1,l_(r_0))`.  Multiplying by
the second gives `(-1,1) in N`, so the nontrivial scalar phase dies in the
normal quotient.  For `|R|=1` there is no moving character: `H_R=K_R=C_2`,
`chi_R` extends, the phase is safe, and the selected representation is already
one-dimensional.  This is exactly the stated scope of the moving-character
obstruction.
