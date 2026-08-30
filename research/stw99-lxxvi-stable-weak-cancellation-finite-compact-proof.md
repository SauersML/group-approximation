---
rg: 2
id: stw99-lxxvi-stable-weak-cancellation-finite-compact-proof
kind: route
title: Recover ideal-local K0 equality and cancel before tensoring
target: stw99-lxxvi-stable-weak-cancellation-finite-compact-injectivity
requires:
  - stw99-lxxvi-ideal-local-k0-protection
---

Let `p,q` be projections over `A` whose Cu classes agree after tensoring with
Z.  Cuntz-equivalent elements generate the same ideal, so
`p tensor 1_Z` and `q tensor 1_Z` generate the same ideal.  The ideal generated
by `p tensor 1_Z` is `Ideal(p) tensor Z`, and similarly for `q`.  Applying a
slice map on Z to the equality of these tensor ideals gives

```text
Ideal(p)=Ideal(q)=:J.
```

Since `A tensor Z` is stably finite, so is its ideal `J tensor Z`.  The
contrapositive of
`stw99-lxxvi-ideal-local-k0-protection` gives

```text
[p]=[q] in K_0(J).
```

The projections each generate the same ideal `J`, so stable weak
cancellation gives `p` Murray--von Neumann equivalent to `q` before
tensoring.  Their original compact Cu classes are therefore equal.
