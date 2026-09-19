---
rg: 2
id: berlai-residue-class-kernel-decomposition
kind: route
title: Split the cyclic kernel into residue classes
target: berlai-nonresidual-one-relator-families-sofic
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

Berlai, *A new family of sofic one-relator groups*, International Journal of
Algebra and Computation 36 (2026), 115--120,
doi:10.1142/S0218196725500444, Theorems A and C and Corollary B.

For `n=1`, `G_{a,b}(l,k)` is an HNN extension of `BS(l,k)` over a cyclic
subgroup. Baumslag--Solitar groups are residually solvable, hence sofic, and
HNN extensions of sofic groups over amenable subgroups are sofic. Let `K` be
the kernel of the exponent-sum map `G_{a,b}(l,k) -> Z` sending `b` to `1`
and `a` to `0`; then `K` is sofic as a subgroup.

For `n>1`, the same map on `G_{a,b^n}(l,k)` has kernel

```text
K_n = <a_i (i in Z) | a_{i+n}^{-1} a_i^l a_{i+n} = a_i^k>.
```

The relators do not mix residue classes modulo `n`, so `K_n` is the free
product of `n` copies of `K`. Hence `K_n` is sofic, and the extension by
the amenable quotient `Z` is sofic. Replacing `b` by `b^{-1}` handles
`n<0`.

For `G_{a,b^{-n}ab^n}(l,k)`, the exponent-sum kernel splits as a free product
of `n` copies of a bi-infinite chain. Every finite subchain is an iterated
amalgam of the theorem-A blocks over cyclic subgroups, hence sofic; directed
union and free-product permanence make the kernel sofic, and extension by
`Z` finishes.

Finally, Berlai's Lemma 1.1 gives failure of residual solvability when
`k=l+1`, while the Baumslag--Miller--Troeger/Meskin finite-quotient argument
gives failure of residual finiteness for `l notin {0,-1}`. QED
