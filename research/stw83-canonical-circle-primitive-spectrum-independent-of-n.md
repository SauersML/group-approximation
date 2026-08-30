---
rg: 2
id: stw83-canonical-circle-primitive-spectrum-independent-of-n
kind: claim
title: The canonical circle Toeplitz family has N-independent primitive spectrum
distinct_from:
  stw83-circle-connector-canonical-full-corner: that reduces finite connector graphs to the canonical algebras; this classifies the primitive topology of those algebras.
  stw83-canonical-circle-toeplitz-dimension-two-bound: that computes the current nuclear-dimension interval; this shows primitive topology and type-I dimension cannot decide between its endpoints.
---

**ESTABLISHED.**  For

```text
A_N=C*(S^N tensor 1, K tensor C(T))
```

the algebra `A_N` is type I, and `Prim(A_N)` is independent of
`N>=1`.

Its open stratum is one circle `{P_t:t in T}`, where

```text
P_t=K tensor {f in C(T):f(t)=0},
```

and its closed stratum is a second circle
`{Q_lambda:lambda in T}` coming from the quotient `A_N/J~=C(T)`, with
`J=K tensor C(T)`.  The specialization relation is

```text
closure({P_t})={P_t} union {Q_lambda:lambda in T}.       (CPS1)
```

Thus the open sets are ordinary opens inside the `P`-circle, together
with sets of the form

```text
{P_t:t in T} union V
```

for `V` open in the `Q`-circle.  Neither this primitive topology nor the
resulting one-dimensional continuous-trace composition factors depend on
`N`.  They therefore cannot resolve whether `dim_nuc(A_N)` is one or
two.

DERIVATION
[[stw83-canonical-circle-primitive-spectrum-proof]]
