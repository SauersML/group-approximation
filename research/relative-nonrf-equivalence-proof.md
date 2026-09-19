---
rg: 2
id: relative-nonrf-equivalence-proof
kind: route
title: Fill forward and adjoin a malnormal cyclic free factor backward
target: relative-nonrf-target-iff-hyperbolic-nonrf
requires:
  - relatively-hyperbolic-dehn-filling
---

`(1) -> (2)` is the argument in
[[non-rf-hyperbolic-via-relative-dehn-filling]]. Given
`1 != w in R_f(G)`, choose finite-index peripheral fillings that avoid the
finite forbidden sets and preserve `w`. The filled peripherals are finite,
so the filling is word-hyperbolic; the image of `w` remains nontrivial and is
still killed by every finite quotient.

For `(2) -> (1)`, let `H` be word-hyperbolic and not residually finite and put

```text
G = H * <t> = H * Z,       P = <t>.
```

Free products of hyperbolic groups are hyperbolic, so `G` is word-hyperbolic.
The subgroup `P` is infinite cyclic, hence finitely generated and residually
finite; it is quasiconvex. In a free product, `P` equals its normalizer and
distinct conjugates of `P` intersect trivially. Bowditch's Theorem 7.11
therefore says that `G` is hyperbolic relative to the conjugacy class of
`P`, i.e. relative to the single peripheral representative `P`.

Finally choose `1 != h in R_f(H)`. For every homomorphism `phi:G->F` with
`F` finite, the restriction `phi|_H` is a finite quotient of `H`, hence
`phi(h)=1`. The free-factor inclusion `H->G` is injective, so
`1 != h in R_f(G)`. Thus `G` is not residually finite. `QED`

Primary source for the reverse relative-hyperbolicity step: B. H. Bowditch,
*Relatively hyperbolic groups*, Internat. J. Algebra Comput. **22** (2012),
no. 3, 1250016, DOI `10.1142/S0218196712500166`, Theorem 7.11.
Source checked 2026-08-30.
