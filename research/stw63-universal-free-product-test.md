---
rg: 2
id: stw63-universal-free-product-test
kind: claim
title: Problem LXIII is exactly the unitary-orbit problem for the two copies in the full free product
distinct_from:
  stw63-distinct-cu-maps-counterexample: that seeks an invariant separating some concrete pair; this reduces every possible pair and every norm obstruction to one universal pair.
---

Let

```text
F = Z *_(C) Z
```

be the full unital free product, and let `i_0,i_1:Z->F` be its canonical
embeddings.  The following are equivalent:

1. every two unital embeddings of `Z` into every unital C\*-algebra are
   approximately unitarily equivalent;
2. `i_0` and `i_1` are approximately unitarily equivalent in `F`.

Fix a dense sequence `(z_k)` in the unit ball of `Z` and define

```text
Delta = inf_(u in U(F))
        sum_(k>=1) 2^(-k) ||u i_0(z_k)u* - i_1(z_k)||.
```

Then `Delta=0` is equivalent to the two preceding statements.  Thus LXIII
has a negative answer exactly when `Delta>0`, in which case the canonical
free-product pair itself is a counterexample.

More generally, define the same weighted orbit distance `Delta_(phi,psi)` for
any pair in a codomain `B`, using the fixed sequence `(z_k)`.  Then

```text
Delta_(phi,psi) <= Delta.
```

Consequently, a positive lower bound for any concrete quotient pair,
including a reduced free-product representation, is already a universal
counterexample certificate.
