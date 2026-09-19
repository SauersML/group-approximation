---
rg: 2
id: fournier-facio-bounded-block-near-no-go-proof
kind: route
title: Use uniform finite-dimensional unitary recurrence to make the block near action free
target: fournier-facio-bounded-block-near-witness-impossible
requires:
  - fournier-facio-group-is-nonsofic
  - fournier-facio-torsion-free-skeleton
  - fournier-facio-charge-null-monomial-perturbations-impossible
---

Let `phi_mu` be the charged diagonal state.  The null-ideal calculation in
`fournier-facio-charge-null-monomial-no-go-proof` does not use that the
comparison unitaries are monomial until its final step.  Applied to `(FBB2)`,
it shows that `phi_mu` is invariant under every `Ad(B_g)`, that every
multiplication defect of `B` is null in charged column norm, and that
essential freeness transfers from `pi` to `B`.

Put

```text
nu(A)=mu(disjoint_union_(y in A) X_y).                (FBBP1)
```

Because `B_g` maps whole blocks to whole blocks, invariance of `phi_mu` on
their diagonal projections makes `nu` invariant under `alpha_g`.  If
`alpha_(gh)(y)` and `alpha_g(alpha_h(y))` differ, the two block-monomial
images of every vector in `X_y` lie in orthogonal blocks and have distance
`sqrt(2)`.  Near multiplicativity therefore says that the bad blocks have
zero `nu`-charge.  Thus `alpha` is a measure-preserving near action.

It remains to prove freeness.  Fix `eta<1/4`.  Compactness of `U(d)` gives,
uniformly for `1<=d<=m`, an integer `N=N(m,eta)` such that every
`V in U(d)` has

```text
min_(1<=n<=N) ||V^n-I||_op<eta.                       (FBBP2)
```

For example, choose a finite `eta`-net in the finite union of the compact
groups `U(d)`.  Two among `I,V,...,V^N` lie in one net ball; multiplying
their difference by a unitary gives `(FBBP2)`.

Suppose `Fix(alpha_g)` has positive `nu`-charge.  On a fixed block `X_y`,
write `V_y` for the internal unitary of `B_g`.  Partition the fixed blocks
into the finitely many sets on which the least exponent supplied by
`(FBBP2)` is `n`.  For some `1<=n<=N`, a set `Y_n` has positive
`nu`-charge and

```text
||V_y^n-I||_op<eta                    (y in Y_n).      (FBBP3)
```

Iterating the finitely many near-multiplication rows shows, outside a
`mu`-null subset of the basis over `Y_n`, that `B_(g^n)` is arbitrarily close
to `B_g^n`.  Equation `(FBBP3)` then gives

```text
|<B_(g^n) delta_x,delta_x>|>1-2eta                    (FBBP4)
```

on a set of positive `mu`-charge.  But `G` is torsion-free, so `g^n!=1`,
and essential freeness for `B_(g^n)` requires this coefficient to be
arbitrarily small on a conull set.  This contradiction proves
`nu(Fix(alpha_g))=0` for every `g!=1`.

Hence `alpha` is an essentially free measure-preserving near action.  The
Elek--Szabo characterization would make `G` sofic, contradicting
`fournier-facio-group-is-nonsofic`.
