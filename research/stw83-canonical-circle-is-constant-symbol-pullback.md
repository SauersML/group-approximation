---
rg: 2
id: stw83-canonical-circle-is-constant-symbol-pullback
kind: claim
title: The canonical circle Toeplitz algebra is the constant-symbol pullback
distinct_from:
  stw83-circle-connector-canonical-full-corner: that identifies the graph algebra with a concrete Toeplitz-module algebra; this identifies the exact pullback condition inside the coefficient-valued Toeplitz tensor product.
  stw83-canonical-circle-primitive-spectrum-independent-of-n: that computes the primitive topology; this gives an algebraic pullback model and locates the coefficient coupling before passing to primitive ideals.
  stw83-canonical-circle-toeplitz-dimension-two-bound: that gives a three-colour approximation; this structural theorem does not remove its third colour.
---

For `N>=1`, let

```text
T_N=C*(S^N,K),                 q_N:T_N->C(T)
```

be the index-`N` Toeplitz extension, with `q_N(S^N)=z`, and put

```text
A_N=C*(S^N tensor 1, K tensor C(T)).
```

Then, inside `T_N tensor C(T)`,

```text
A_N={x in T_N tensor C(T):
     (q_N tensor id)(x) belongs to C(T) tensor 1}.       (1)
```

Equivalently, after identifying `T_N tensor C(T)` with
`C(T,T_N)` using the coefficient-circle variable,

```text
A_N={x in C(T,T_N): q_N(x(t)) is independent of t}.     (2)
```

Thus the unresolved circle-by-circle graph family is not the full tensor
product of a Toeplitz algebra with a circle.  Its compact ideal may vary over
the coefficient circle, but its corona symbol is forced to be constant in
that variable.  Any dimension-one proof must exploit precisely this
constant-symbol restriction; a product-colouring argument for
`T_N tensor C(T)` discards the only available dimension collapse.

**ESTABLISHED.**

DERIVATION
[[stw83-constant-symbol-pullback-proof]]
