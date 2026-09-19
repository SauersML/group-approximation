---
rg: 2
id: stw99-lxvi-reduced-product-assembles-finite-stages-proof
kind: route
title: Use tail-compatible matrix embeddings and coordinatewise polar correction
target: stw99-lxvi-reduced-product-assembles-finite-stages
requires: []
---

First, the unit of `Q` is finite.  Suppose `x in Q` is an isometry and
choose a bounded representative `(x_n)` in `prod_n A_n`.  Then

```text
||x_n* x_n-1|| -> 0.
```

For all sufficiently large `n`, set

```text
y_n=x_n (x_n* x_n)^(-1/2).
```

The elements `y_n` are isometries, and `||y_n-x_n|| -> 0`.  Finiteness of
`A_n` makes every `y_n` unitary.  It follows that
`||x_n x_n*-1|| -> 0`, so `x` is unitary in `Q`.

Fix standard compatible inclusions

```text
M_(2^k) -> M_(2^n),       z |-> z tensor 1_(2^(n-k))       (n>=k),
```

and follow them by the given unital embeddings into `A_n`.  For
`z in M_(2^k)`, let `Phi_k(z)` be the class in `Q` of the sequence which is
zero before coordinate `k` and is the resulting image of `z` at every
coordinate `n>=k`.  The maps `Phi_k` are isometric unital embeddings into
`Q`: omitting finitely many unit coordinates does not change the unit in the
quotient.  Moreover,

```text
Phi_(k+1)(z tensor 1_2)=Phi_k(z),
```

because the representing sequences agree from coordinate `k+1` onward.
They therefore induce a unital embedding

```text
M_(2^infinity) -> Q.
```

Finally choose, for each `n`, an isometry `v_n in M_2(A_n)` with proper
range.  Under the canonical identification

```text
M_2(Q) = (prod_n M_2(A_n))/(directSum_n M_2(A_n)),
```

the class `v=(v_n)` is an isometry.  Each nonzero defect projection
`1-v_n v_n*` has norm one, so the defect sequence does not belong to the
direct sum.  Hence `v` has proper range and the unit of `M_2(Q)` is infinite.
