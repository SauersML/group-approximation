---
rg: 2
id: nonce-factor-in-group-factor-corner-forces-nonhyperlinear
kind: claim
title: A trace-preserving non-CE algebra in a positive group-factor corner forces nonhyperlinearity
distinct_from:
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that starts with an algebraic map into a group-algebra corner and assumes every BCS trace is non-CE; this treats a specified tracial von Neumann algebra and an arbitrary projection in the group factor.
  non-ru-bcs-is-satisfiable-in-a-group-factor: that is the BCS-specialized open construction of the host; this is the general completed implication once a trace-preserving model is given.
  unique-trace-signed-corner-quotient-forces-nonhyperlinear: that promotes trace through uniqueness and a quotient; this assumes the desired trace is preserved by an injective corner embedding.
---

**ESTABLISHED.**  Let `(M,tau_M)` be a finite tracial von Neumann algebra
which is not Connes embeddable.  Let `G` be countable and let `0!=p in L(G)`
be a projection.  If there is a normal injective unital, trace-preserving map

```text
Phi:(M,tau_M) -> (pL(G)p, tau_G(p . p)/tau_G(p)),                   (NGC1)
```

then `G` is nonhyperlinear.

If `M` is a finite factor, trace preservation is automatic for a normal
unital embedding because both algebras use normalized traces and the factor
has a unique normalized trace.  For a general tracial algebra it is not
automatic: a non-trace-preserving embedding could select a different,
Connes-embeddable trace and does not prove the conclusion.

For a finite subgroup `K<=G`, the averaging projection

```text
p_K=|K|^-1 sum_(k in K) k
```

has canonical trace `1/|K|`, so `(NGC1)` applies verbatim to
`p_KL(G)p_K`.
