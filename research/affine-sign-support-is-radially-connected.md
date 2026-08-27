---
rg: 2
id: affine-sign-support-is-radially-connected
kind: claim
title: Every affine sign-support is connected in an exact simplex radial presentation
distinct_from:
  radial-parallelograms-kill-simplex-class-two: that detects alternating commutator characters by radial pairs; this is an ordinary support-connectivity theorem for one linear character.
  expander-edge-overlay-detects-simplex-exterior-square: that gives a quantitative edge density for two affine words; this needs no expansion and proves qualitative connectivity from minimum distance and exact code equality.
---

Assume `n>=3` and that the kernel of the radial parity checks on `K^*` is
exactly the punctured affine simplex code

```text
C={x |-> a+ell(x): a in F_2, ell in K}.               (ASC1)
```

Join two coordinates when they occur in one radial four-set.  For every
nonzero `u in C`, the graph induced on `supp(u)` is connected.

To prove this, let `S_0` be one connected component of `supp(u)`.  Every
radial check meets `supp(u)` evenly.  Moreover all support vertices in one
check are pairwise joined, so they lie in one component.  Therefore every
check meets `S_0` evenly and `1_(S_0)` is itself a codeword in `C`.

The nonzero weights of the punctured affine simplex code are

```text
2^(n-1)-1,  2^(n-1),  2^n-1.                         (ASC2)
```

For a nonconstant `u`, two nonempty components would each have weight at
least `2^(n-1)-1`, whose sum exceeds `wt(u)` for `n>=3`.  For the constant
word, the whole coordinate graph is connected because every `x` is joined
to `alpha x` and `alpha` generates `K^*`.  This proves the claim.
