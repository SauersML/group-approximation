---
rg: 2
id: exact-fd-invisibility-no-robustification-proof
kind: route
title: Apply a hypothetical collapse modulus to the Slofstra--Vidick sofic group
target: exact-fd-invisibility-has-no-general-hs-robustification
requires: []
---

**Established by citation and one ultraproduct contradiction.**
Slofstra--Vidick, *Entanglement in non-local games and the hyperlinear
profile of groups*, arXiv:1711.10676, Proposition 3.2 and the paragraph
immediately following it, supply the finitely presented group `K`, its soficity,
and the exact finite-dimensional invisibility of the nontrivial central
involution `c`.

Since `K` is sofic, it is hyperlinear.  Canonical-trace matrix microstates
`U_n` satisfy

```text
def(U_n)->0,
tr(c(U_n))->0,
||c(U_n)-I||_2^2->2.                                  (ENR1)
```

A modulus `(EFI1)` would force the last quantity to tend to zero, contradicting
`(ENR1)`.  Thus exact invisibility does not provide approximate normalized-HS
collapse, even with finite presentation and soficity.

