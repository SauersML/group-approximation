---
rg: 2
id: range-local-affine-edge-proof
kind: route
title: Decompose a commuting edge-selector product and use faithfulness of the canonical trace
target: range-local-finite-edge-authentication-is-affine
requires: []
---

Put `L=EA`.  Since `E` and `A` commute, `I=E intersect A` is central in
`E`.  Let `eta` be its scalar character in `sigma`.  For every
`chi in C_sigma`, the formula

```text
pi_chi(ea)=sigma(e)chi(a)                              (RFEP1)
```

is a well-defined representation of `L`: changing `ea` by an element of
`I` changes the two factors by reciprocal copies of `eta`.

The representations `pi_chi` are pairwise inequivalent, their dimensions
are `dim(sigma)`, and the number of compatible characters is

```text
|C_sigma|=|A|/|I|=[L:E].                              (RFEP2)
```

Frobenius reciprocity, followed by the dimension count in `(RFEP2)`, gives

```text
Ind_E^L(sigma)=directSum_(chi in C_sigma) pi_chi.      (RFEP3)
```

Equivalently, in the left regular representation of `L`,

```text
e_sigma p_chi !=0                 (chi in C_sigma).    (RFEP4)
```

The coefficient of the identity can be evaluated directly.  In the product
of the two character-idempotent sums, `ea=1` exactly when
`e=i in I` and `a=i^(-1)`.  Compatibility makes every one of the `|I|`
summands positive, giving

```text
tau(e_sigma p_chi)
 =dim(sigma)^2 |I|/(|E||A|).                          (RFEP4a)
```

If `e_sigma<=q<=p_R`, then `(RFEP4)` is impossible for a compatible
`chi` outside `R`; this proves `C_sigma subset R`.

For the canonical saturation statement, use the exact HNN identity

```text
t e_(sigma_0)t^(-1)=e_sigma.
```

Then

```text
||(1-q)t e_(sigma_0)||_(2,tau_Gamma)^2
 =tau_Gamma(e_sigma(1-q)e_sigma).                     (RFEP5)
```

Canonical matrix microstates converge on every fixed group-algebra
polynomial, so an `o(1)` version of the left side forces the right side to
vanish.  Faithfulness of `tau_Gamma` gives `(1-q)e_sigma=0`.  When the
finite packet embeds, this equality is already an equality in its finite
group algebra.  The affine-support conclusion therefore applies before any
rounding or dimension estimate.

Finally, for finitely many contexts, the affine cosets `C_(sigma,c)` are
specified by finitely many parity equations.  Exact pulled-back context
measurements supported on those cosets, together with exact shared-variable
consistency, are exactly a commuting solution of the resulting LCS.  Since
each coset is contained in the original allowed predicate, finite-strategy
soundness transfers by a fixed finite telescoping/union-bound estimate.
