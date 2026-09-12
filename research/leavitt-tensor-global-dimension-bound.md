---
rg: 2
id: leavitt-tensor-global-dimension-bound
kind: claim
title: Tensoring with d copies of L_k(1,2) raises global dimension by at most d, and L^(⊗d) has global dimension exactly d
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that is vanishing of K_1 and K_2 for three or more factors; this is a global dimension bound, the regularity half of the regular coherence that implies it.
---

**ESTABLISHED.** Let `k` be a field, `L = L_k(1,2)`, `B` a `k`-algebra and
`d >= 1`. Then

```text
l.gl.dim(B ⊗_k L^(⊗d)) <= l.gl.dim B + d,
```

and the same holds for right global dimensions. With `B = k`,
`l.gl.dim L^(⊗d) = d`.

**Consequence.** Every module over `L^(⊗d)`, and over `B ⊗ L^(⊗d)` whenever
`l.gl.dim B < ∞`, has finite projective dimension. These rings would be regular
coherent if they were coherent. For `d >= 2`, `L^(⊗d)` is not coherent
(`leavitt-tensor-powers-are-not-left-coherent`), so this bound does not feed
`regular-coherent-coefficients-kill-leavitt-tensor-k-theory` for tensor powers.
