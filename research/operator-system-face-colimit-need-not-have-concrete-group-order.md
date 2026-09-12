---
rg: 2
id: operator-system-face-colimit-need-not-have-concrete-group-order
kind: claim
title: Local Fourier face orders do not formally determine the concrete group operator-system order
distinct_from:
  chordal-partial-positive-operator-matrices-lift: that gives a positive completion theorem under chordality; this gives a nonchordal two-axis counterexample where the universal colimit order is strictly larger than the concrete group order.
  triangle-relator-extension-admits-local-ucp-sections: that asks for ucp lifts for one triangle quotient; this refutes only the formal claim that its cyclic matrix order follows automatically by taking the operator-system colimit of the finite face orders.
---

**ESTABLISHED.**  Let

```text
Delta={(0,0),(+-1,0),(0,+-1)} subset Z^2.
```

The universal operator system `UOS(Delta)` obtained as the coproduct/colimit
of the two one-axis sums-of-squares systems is not completely order
isomorphic to the concrete Fourier operator system

```text
C^*(Z^2)_(Delta) subset C^*(Z^2).
```

Indeed, the C-star envelope of the universal system is `C^*(F_2)`, while the
C-star envelope of the concrete system is `C^*(Z^2)`.  Hence the canonical
map from the universal colimit order to the concrete Fourier order is not a
complete order embedding.  Equivalently, the complete factorisation and
complete positive-extension properties fail for this elementary cross.

Proof: `z2-cross-operator-system-colimit-gap-citation`.

Therefore an operator-system colimit describes the concrete group matrix
order only after an additional factorisation/extension theorem.  Pairwise or
facewise positivity is not formal cyclic positivity, even for an abelian
group and two one-dimensional faces.
