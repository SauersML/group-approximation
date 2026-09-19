---
rg: 2
id: ssa-self-kunneth-exact-k-theory-criterion
kind: claim
title: SSA self-Kunneth is exactly unit-insertion surjectivity plus vanishing self-Tor
artifacts:
  - research/artifacts/ssa-self-kunneth-xiv2-audit-2026-08-31.md
---

**ESTABLISHED.** Let `D` be strongly self-absorbing, put

```text
G=K_*(D)=G_0 (+) G_1,       u=[1_D] in G_0,
```

and let `alpha:G tensor G -> K_*(D tensor D)` be the graded external-product
map. Then `alpha` is always split-surjective. Moreover, the Kunneth short exact
sequence for `(D,D)` holds if and only if

```text
j:G -> G tensor G,       j(x)=x tensor u
```

is an isomorphism and `Tor(G,G)=0` in both graded degrees. In fact `j` is
always split-injective, so only its surjectivity is open.

Under these equivalent conditions,

```text
K_1(D)=0,
K_0(D) -> K_0(D) tensor K_0(D),  x |-> x tensor [1_D]
```

is an isomorphism, and `Tor(K_0(D),K_0(D))=0`. Equivalently, the
self-Kunneth sequence holds precisely when `K_1(D)=0` and tensor
multiplication makes `K_0(D)` a torsion-free solid ring with unit `[1_D]`.
Thus a
failure of SSA self-Kunneth has only two possible locations: a nonzero kernel
of the already-surjective external product, or a nonzero algebraic self-`Tor`
term.

In particular, `K_1(D)=0` is a consequence of self-Kunneth here, not an
unconditional consequence of strong self-absorption.
