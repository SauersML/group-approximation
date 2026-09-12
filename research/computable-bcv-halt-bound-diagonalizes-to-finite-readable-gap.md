---
rg: 2
id: computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap
kind: claim
title: A computable BCV HALT readable bound would diagonalize to a finite-readable NONHALT gap
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that diagonalizes the unrestricted ZPC-IRS value and obtains no orbit bound; this conditional statement diagonalizes a bounded-factor value.
  bcv-halt-completeness-has-computable-readable-factor-bound: that was the required uniformity premise and is now refuted by the universal backward-compression lower bound.
  perfect-gap-zpc-has-finite-readable-translate-algebra: that directly asks for a finite-factor gap witness; this conditional implication does not supply one because its antecedent is false.
---

**VALID CONDITIONAL; PREMISE REFUTED.** If there were a total computable
function `B(M)`, independent of halting time, such that every halting
machine's BCV game `G_M` had a perfect ZPC strategy with

```text
dim D_infinity <= B(M),                                  (CBD1)
```

then the bounded-factor diagonal argument would produce a nonhalting
machine `M_0` with a ZPC-IRS strategy satisfying

```text
omega_ZIRS^(B(M_0))(G_(M_0)) = 1,
omega*(G_(M_0)) <= 1/2,
dim D_infinity <= B(M_0).                                (CBD2)
```

The implication remains mathematically correct. It is unusable in the BCV
fixed point: `bcv-no-computable-perfect-halt-readable-bound` proves that
no total computable `B` satisfying `(CBD1)` exists. In fact, for a
machine halting at tower depth `h`, every perfect strategy has readable
dimension at least `2^h`.

Therefore this node does not establish `(CBD2)`, does not establish
`perfect-gap-zpc-has-finite-readable-translate-algebra`, and contributes
no surviving route to a nonhyperlinear group.
