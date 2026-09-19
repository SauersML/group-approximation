---
rg: 2
id: whitehead-one-relator-via-waldhausen-class-cl
kind: route
title: Put every subgroup of a torsion-free one-relator group in Waldhausen's class Cl
target: whitehead-vanishing-torsion-free-one-relator
requires: [whitehead-is-degree-one-assembly-cokernel]
---

Use Friedhelm Waldhausen, *Algebraic K-theory of generalized free products,
Part 2*, Annals of Mathematics (2) 108 (1978), 205--256,
doi:10.2307/1971166.

Definition 19.2 defines the class `Cl`. Theorem 19.5(4), printed on page 250
with its proof on pages 251--252, states that every torsion-free one-relator
group belongs to `Cl`. The proof runs the Magnus--Moldavanskii hierarchy:
after embedding when necessary, each stage is an HNN extension of a
shorter-relator group over finitely generated free groups; Definition
19.2(2) propagates membership back up the hierarchy.

Proposition 19.3(1), printed on page 249, says that `Cl` is closed under
arbitrary subgroups. Its covering-space proof imposes no finite-generation,
finite-presentation, or finite-index condition. Hence if `H<=G`, then
`H` also belongs to `Cl`.

Theorem 19.4, beginning on printed pages 249--250, states that if `R` is
regular noetherian and `G` belongs to `Cl`, then `Wh_R(G)` is
contractible. Take `R=Z`, which is regular noetherian. Thus `Wh_Z(H)` is
contractible, so the integral assembly

```text
K(BH; Z) -> K(ZH)
```

is a homotopy equivalence. In degree one it is surjective, and
[[whitehead-is-degree-one-assembly-cokernel]] identifies its cokernel with
`Wh(H)`. Hence `Wh(H)=0`. QED

This proves only the regular-noetherian, untwisted algebraic K-theory
statement. It does not prove the Full Farrell--Jones conjecture for
torsion-free one-relator groups. The torsion-free hypothesis also cannot be
removed: one-relator groups with torsion can have nonzero Whitehead groups.
