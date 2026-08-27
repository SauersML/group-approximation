---
rg: 2
id: binary-leavitt-hyperlinear-iff-singular-near
kind: claim
title: Binary Leavitt hyperlinearity is exactly existence of a purely singular essentially free near representation
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that is the unresolved yes/no question; this gives an equivalent witness problem with the normal sector completely removed.
  hyperlinear-near-representation-criterion: that applies to every group and permits arbitrary invariant states; this specializes to the first nonsofic group and proves every valid state witness must be purely singular.
---

For

```text
Q=L_(F_2)(1,2)^x,
```

the following are equivalent.

1. `Q` is hyperlinear.
2. There exist a Hilbert space `H`, a **purely singular** state `phi` on
   `B(H)`, and a `phi`-near representation `pi:Q -> U(H)` such that

   ```text
   phi(pi(g))=0                    for every g != 1.     (BLPS1)
   ```

The reverse implication is exactly the state form of the Kahl--Schneider
hyperlinearity criterion.  For the forward implication, that criterion first
produces an arbitrary invariant free near-state.  The established minimal
almost periodicity of `Q`, together with
`map-free-near-state-is-purely-singular`, forces its normal component to
vanish.

Hence the binary Leavitt hyperlinearity fork is now localized to one genuinely
singular phenomenon.  No trace-class density, finite-rank exhaustion, normal
hypertrace, or countably additive atomic diagonal state can witness a positive
answer.
