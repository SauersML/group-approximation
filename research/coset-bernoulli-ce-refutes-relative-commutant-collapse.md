---
rg: 2
id: coset-bernoulli-ce-refutes-relative-commutant-collapse
kind: claim
title: Connes embeddability of the coset Bernoulli crossed product refutes relative-commutant collapse
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that asserts commutant equality in every matrix ultraproduct; this gives an explicit crossed-product obstruction whose Connes embeddability would refute it.
  sl3-pair-relative-commutant-route: that proposes a higher-rank pair with a Kazhdan subgroup; this obstruction applies to every proper subgroup pair, including both arithmetic pairs.
  coset-tower-automorphic-dilation: that builds an infinite tower for a proper endomorphism; this uses the single homogeneous space A/C and tests the relative commutant directly.
---

Let `C<A` be a proper subgroup, let `(K,kappa)` be a nontrivial finite
probability space, and put

```text
X=K^(A/C),
N=L^infinity(X) rtimes A.                              (CB1)
```

Write `u_a` for the canonical group unitaries.  The map

```text
pi:A->U(N),    a |-> u_a                              (CB2)
```

has the regular group trace.  If `f in L^infinity(K)` is a nonconstant
circle-valued function and `v(x)=f(x_C)` is the corresponding unitary in the
coordinate indexed by the base coset `C`, then

```text
v in pi(C)' cap N,                                    (CB3)
```

because every element of `C` fixes the coset `C`.  For every `a notin C`,
the Bernoulli coordinates `C` and `aC` are independent and `a` moves the
distinguished coordinate, so

```text
[v,pi(a)] != 0.                                       (CB4)
```

Consequently, if `N` is Connes embeddable, an embedding of `N` into a
tracial matrix ultraproduct gives a regular-trace representation of `A` for
which

```text
pi(C)' cap M != pi(A)' cap M.                         (CB5)
```

Thus Connes embeddability of `(CB1)` refutes the relative-commutant-collapse
claim for the pair `C<A`.  Contrapositively, relative-commutant collapse
implies that the explicit generalized Bernoulli crossed product `(CB1)` is
not Connes embeddable.

This is a genuine conditional firewall, not an unconditional counterexample.
For the arithmetic inclusions

```text
SL_n(Z) < SL_n(Z[1/2]),
```

the action on `A/C` has nonamenable stabilizer `C`.  Standard sofic-group
Bernoulli results concern the regular index set `A` (or actions already known
to be sofic); they do not prove that this generalized coset action is sofic
or that `(CB1)` is Connes embeddable.  That embeddability question is itself
the hard matrix-coordinate content.

## Attempts

- **Treat `A` sofic as enough.**  Invalid: a sofic group need not have every
  action sofic, and the stabilizer of `A/C` is the nonamenable group `C`.
- **Use a finite quotient action.**  Co-density makes `C` surject onto every
  relevant finite quotient of `A`, so no finite quotient retains a
  `C`-fixed but `A`-moved coordinate.
- **Use the quasi-regular representation abstractly.**  The vector at `C`
  is `C`-fixed and not `A`-fixed, but `l2(A/C)` is weakly contained in the
  regular representation only when `C` is amenable.  The required
  finite-coordinate realization is precisely the missing CE statement.
