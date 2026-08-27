---
rg: 2
id: collective-centralizer-cycles-free-gauge-proof
kind: route
title: Conjugate pair commutators into differences of vertex gauges and telescope
target: collective-centralizer-cycles-are-free-gauge-identities
requires: []
---

Direct free reduction gives

```text
r_(ij)^(h_j^(-1))
 = h_j [b,h_i^(-1)h_j] h_j^(-1)
 = h_j b^(-1) h_j^(-1) h_i b h_i^(-1).
```

On the other hand,

```text
Q_j
 = h_j [b,h_j] h_j^(-1)
 = h_j b^(-1)h_j^(-1)b,

Q_i^(-1)
 = (h_i b^(-1)h_i^(-1)b)^(-1)
 = b^(-1)h_i b h_i^(-1).
```

Multiplying cancels the adjacent `bb^(-1)` and proves `(CGI1)`.
Taking inverses gives

```text
(r_(ij)^(h_j^(-1)))^(-1)=Q_iQ_j^(-1).
```

The ordered product along a directed path telescopes to
`Q_(i_0)Q_(i_k)^(-1)` by free cancellation.  It is therefore the empty word
for a directed cycle, proving `(CGI2)` and the zero-area assertion.
