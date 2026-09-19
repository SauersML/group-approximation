---
rg: 2
id: free-bernoulli-group-realizability-proof
kind: route
title: Use free products and restricted wreath products, then restrict to one coordinate
target: group-realizability-reflects-free-bernoulli-envelopes
requires: []
---

Suppose first that `j:Q->L(Lambda)` is a unital trace-preserving embedding.
Reduced free-product functoriality gives

```text
j * id : Q * L(Gamma) -> L(Lambda) * L(Gamma)
                         = L(Lambda * Gamma),                  (GRP1)
```

again unitally and trace preservingly.  Conversely the canonical first
free-product leg embeds `Q` trace preservingly in `Q*L(Gamma)`.  Restricting
any group-factor embedding of the latter proves the reverse implication in
`(GRB1)`.

For the Bernoulli envelope, tensor `j` over `I`.  The standard product-trace
identification gives an equivariant embedding

```text
Q^(tensor I) -> L(Lambda)^(tensor I)=L(Lambda^(I)),            (GRP2)
```

where `Lambda^(I)` is the restricted direct sum and `Gamma` permutes its
coordinates through the given action on `I`.  Passing to crossed products
gives

```text
Q^(tensor I) rtimes Gamma
 -> L(Lambda^(I) rtimes Gamma),                               (GRP3)
```

with preservation of the canonical trace.  This proves the forward
implication of `(GRB2)`.  For the reverse implication choose one
`i_0 in I`; its tensor coordinate is a unital trace-preserving copy of `Q`
inside the Bernoulli base and hence inside the crossed product.  Restricting
an assumed group-factor embedding of the envelope to that coordinate proves
that `Q` was group-realisable.

The reverse arguments use no freeness, action, or cocycle hypothesis: any
tracial envelope which literally contains the input already reflects
group-factor realizability.  What is special to `(GRP1)--(GRP3)` is the
forward direction, which compiles an existing host by ordinary free products
and an untwisted coordinate permutation.  A general operator-valued cocycle
action need not extend through `j`, so the theorem does not assert a false
compiler for the CDI envelope.

