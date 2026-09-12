---
rg: 2
id: sl3-prime-permutation-codensity
kind: claim
title: The integral SL3 lattice is permutation co-dense in every one-prime S-arithmetic enlargement
distinct_from:
  arithmetic-finite-actions-are-lambda-generated: that is the p=3 instance used by the summit wreath; this is the prime-uniform statement needed by the large-prime centralizer-HNN and coset-action fork.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that is finite-dimensional unitary-representation co-density for a rank-one pair; this is equality of images in every finite permutation action for the rank-two pair.
---

Fix a prime `p` and put

```text
Lambda = SL_3(Z),                 Gamma_p = SL_3(Z[1/p]).        (PPC1)
```

For every homomorphism to a finite group,

```text
q : Gamma_p -> Q,                 q(Lambda)=q(Gamma_p).          (PPC2)
```

Equivalently, for every finite action `rho:Gamma_p->Sym(V)`,
`rho(Lambda)=rho(Gamma_p)`.  Consequently:

1. the closure of `Lambda` in the profinite topology of `Gamma_p` is all of
   `Gamma_p`; in particular `Lambda` is not separable in `Gamma_p` and
   `Gamma_p` is not LERF;
2. `Lambda` is not a Chabauty limit of finite-index subgroups of `Gamma_p`
   (the rooted-Schreier, or subgroup-co-sofic, approximation);
3. every finite `Gamma_p`-equivariant quotient of the transitive set
   `Gamma_p/Lambda` is the one-point set.

The proof is the same congruence argument as the established `p=3` theorem.
The congruence subgroup property for `SL_3(Z[1/p])` puts a principal
congruence subgroup of some level `m`, with `(m,p)=1`, inside the kernel of
`q`.  Hence `q` factors through the image of `SL_3(Z[1/p])` modulo `m`.
Because `p` is a unit modulo `m`, that image is `SL_3(Z/m)`, and reduction
`SL_3(Z)->SL_3(Z/m)` is onto.  Thus the integral subgroup already maps onto
the full finite image, proving `(PPC2)`.  The statement for a finite action
is obtained by applying this to its image.

For the last assertion, a finite equivariant quotient of
`Gamma_p/Lambda` is `Gamma_p/H` for a finite-index subgroup `H` containing
`Lambda`.  Equation `(PPC2)` applied to the action on `Gamma_p/H` says that
the `Lambda`-orbit of `H` equals the full `Gamma_p`-orbit; the former is the
single point `H`, so `H=Gamma_p`.

For the second assertion, suppose finite-index subgroups `H_n` converged to
`Lambda` in the Chabauty topology.  Since `Lambda` is finitely generated,
all of a fixed finite generating set belongs to `H_n` for sufficiently
large `n`, so `Lambda<=H_n`.  But `(PPC2)` applied to the action on
`Gamma_p/H_n` forces `H_n=Gamma_p`.  Such a sequence cannot exclude any
fixed `g in Gamma_p\Lambda`, contradicting Chabauty convergence.

**Trust surface.**  This is only the parameter-uniform form of
`arithmetic-finite-actions-are-lambda-generated`; it uses the same CSP and
strong-approximation input recorded and proved there, and imports no new
external result.

DERIVATION
sl3-prime-permutation-codensity-proof
