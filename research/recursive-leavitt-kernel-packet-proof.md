---
rg: 2
id: recursive-leavitt-kernel-packet-proof
kind: route
title: Separate the iterated constant S3 layers and induct on the recursive support
target: recursive-leavitt-kernel-packets-are-locally-finite
requires: []
artifacts:
  - research/artifacts/recursive-leavitt-kernel-packet-tower-2026-08-21.md
---

## Direct proof

Scalar matrices commute with constant matrices under the Leavitt
self-similarity, so `delta(G)` centralizes `H`.  If `i<j`, applying `delta^i`
to the fact that `H` centralizes `delta^(j-i)(H) <= delta(G)` shows that
`delta^i(H)` centralizes `delta^j(H)`.  Thus `H_n` is a quotient of the finite
direct product `H^(n+1)` and has order at most `6^(n+1)`.

Both `z=[1]+[g]+[g^2]` and the four-term idempotent
`f=[1]+[u]+[v]+[g]` are supported in `H`.  The recursive map is

```text
lambda(a)=delta_*(a)f.
```

If `a` is supported in `H_n`, then `delta_*(a)` is supported in
`<delta(H),...,delta^(n+1)(H)>`; multiplying by `f` puts `lambda(a)` in
`F_2[H_(n+1)]`.  Starting from `q_0=z in F_2[H_0]` proves the support claim by
induction.

Every finite set of the `q_n` is therefore contained in one finite group
algebra `F_2[H_N]`.  Finite group algebras are finite-dimensional and directly
finite, and a directed union of directly finite unital subrings is directly
finite because any proposed one-sided inverse pair occurs in one stage.
