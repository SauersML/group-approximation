---
rg: 2
id: agent-free-compressor-padded-j-row-proof
kind: route
title: Pad the quotient lists by one and telescope the conditional row through the HNN letter
target: agent-free-compressor-padded-j-row-kills-payload-root
requires:
  - finite-inclusion-is-free-self-compressor-quotient
---

Choose generating lists for `B` and `A`, pad them by identities as necessary,
and add one paired entry

```text
b_0=1,                         a_0=J.
```

In the long-marker construction choose a fixed lift `R_0` of `J` and put

```text
alpha(x_i)=x_i^M R_i x_i^M
```

with `M` a sufficiently large multiple of the exponent of `B`.  The proof of
`finite-inclusion-free-compressor-proof` applies verbatim: the initial and
terminal `x_i^M` markers prevent cancellation in every reduced source word,
and the abelianization determinant is greater than one for large `M`.
Therefore `alpha` is injective and proper.  The equations
`theta(alpha(x_i))=a_i` show that its quotient image remains exactly `A`, and
give `(PJR2)` for `i=0`.

Write `u_w` for the coefficient unit attached to a free word.  The `x_0`
instance of `(BCL0)` is

```text
Pu_(x_0)=P.                                               (1)
```

The commutation rows `[P,u_(x_i)]=0` and the identification rows
`P(u_(x_i)-theta(x_i))=0` telescope through the one fixed word
`alpha(x_0)` (including inverse letters), and hence

```text
Pu_(alpha(x_0))=P theta(alpha(x_0))=PJ=-P.              (2)
```

On the other hand, `[P,t]=0`, the HNN row, and `(1)` give

```text
Pu_(alpha(x_0))
 =P t u_(x_0)t^(-1)
 =t P u_(x_0)t^(-1)
 =tPt^(-1)=P.                                           (3)
```

Comparing `(2)` and `(3)` proves `2P=0`.  Since `p` is odd, `P=0`.
Root additivity gives

```text
x_ij(P)^2=x_ij(2P)=1,
```

while every root has exponent `p`.  Coprimality of `2` and `p` proves
`(PJR4)`.

Every displayed coefficient and root calculation uses a fixed finite word
and a fixed number of defining relators.  Replacing equalities by
normalized-HS defects and telescoping yields `(PJR5)`.  No spectral rounding,
rank extraction, or ambient-dimension-dependent estimate enters.

