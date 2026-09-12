---
rg: 2
id: collective-centralizer-cycles-are-free-gauge-identities
kind: claim
title: Collective centralizer cycles are free gauge identities
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that proves individual and mean pair filling areas diverge for escaping finite-mark centralizer packets; this identifies the exact cycle-space kernel which appears when those large loops are multiplied collectively.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that is an axis obstruction to one-cell edge templates; this is a free-word telescoping identity showing why an apparently stronger many-edge product certificate can carry no information at all.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that is a model-level private-gauge firewall; this is the exact free-group gauge identity underlying cycle cancellation of centralizer corrections.
---

Use the conventions

```text
[u,v]=u^(-1)v^(-1)uv,
u^v=v^(-1)uv.
```

For arbitrary free-group words `b,h_1,...,h_M`, put

```text
r_(ij)=[b,h_i^(-1)h_j],
Q_i=[b,h_i]^(h_i^(-1)).
```

Then the following is a literal freely reduced identity, using no relator:

```text
r_(ij)^(h_j^(-1)) = Q_j Q_i^(-1).                       (CGI1)
```

Consequently every directed cycle `i_0,i_1,...,i_k=i_0` obeys

```text
product_(s=0)^(k-1)
  (r_(i_s,i_(s+1))^(h_(i_(s+1))^(-1)))^(-1) = 1         (CGI2)
```

by adjacent free cancellation.  The collective boundary in `(CGI2)` has
zero filling area even when every individual `r_(ij)` has arbitrarily large
filling area.

Thus multiplying centralizer corrections around cycles cannot evade the
twisted-Schreier obstruction in a useful way: it erases the target errors as
a free gauge tautology.  A viable collective Carmichael compiler must retain
positive information about the individual normalized-HS defects, for example
by orthogonalizing edge errors or proving a sum-of-squares inequality.  One
scalar product diagram, even one containing arbitrarily many edges, cannot
provide that information merely through cycle cancellation.
