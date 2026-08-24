---
rg: 2
id: finite-character-packing-extension-is-clique-lp-proof
kind: proof
title: Proof that finite character packing-extension is a clique and linear program
proves:
  - finite-character-packing-extension-is-clique-lp
---

For each pair `(i,g)` put

```text
p_(i,g)=g e_(H_i,chi_i) g^(-1) in C[G].               (CLQ1)
```

Identify two pairs when they give the same projection and use the resulting
finite set as the vertex set of `X_G`; retain `i` as its colour.  Declare
two different vertices adjacent when their projections multiply to zero.
By `finite-character-hecke-intersection-formula`, this is equivalent to
disagreement of the transported characters on `(CLP2)`, so adjacency is
computed from the multiplication table of `G` and the finite character
tables.  A set of projections is pairwise orthogonal exactly when the
corresponding vertices form a clique.  The colour multiplicities in that
clique are precisely the requested numbers of conjugates.

Every tracial state on the finite-dimensional algebra `C^*(G)` is a convex
combination of the normalized irreducible traces:

```text
tau=sum_(pi in Irr(G)) lambda_pi tr_pi,                (CLQ2)
```

with `(lambda_pi)` satisfying `(CLP3)`.  If

```text
Res_(H_i)^G pi
  isomorphic to directSum_(sigma in Irr(H_i))
    sigma^[Res pi:sigma],                              (CLQ3)
```

then the normalized trace of the `sigma`-isotypic central projection is

```text
[Res pi:sigma] dim(sigma)/dim(pi).                    (CLQ4)
```

Taking the convex combination `(CLQ2)` proves that restriction of `tau` to
`C^*(H_i)` has distribution `mu_i` exactly when `(CLP4)` holds.  This proves
the claimed equivalence.

All coefficients in `(CLP3)--(CLP4)` are rational.  If the system is
feasible over the reals, its nonempty rational polytope contains a rational
point.  If it is infeasible, the rational form of Farkas separation gives a
rational dual witness.  The graph is finite, so a coloured clique can be
exhibited directly and nonexistence can be checked by exhaustive finite
search.  These are the stated certificates.
