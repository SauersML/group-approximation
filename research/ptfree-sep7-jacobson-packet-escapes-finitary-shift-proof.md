---
rg: 2
id: ptfree-sep7-jacobson-packet-escapes-finitary-shift-proof
kind: route
title: Apply the Laurent symbol to distinguish the finite packet from the finitary kernel
target: ptfree-sep7-jacobson-packet-escapes-finitary-shift
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - binary-jacobson-active-cycle-generates-rank-three
artifacts:
  - research/artifacts/ptfree-sep7-jacobson-symbol-audit.md
---

The first prerequisite identifies the symbol kernel with `L`. Since
`sigma(Q)=0`, the symbol on `F_2[Q]=F_2 Q + F_2(1-Q)` sends
`alpha Q + beta(1-Q)` to `beta`. Entrywise application on the finite
packet is therefore exactly the projection

```text
G_Q x G_P -> G_P=EL_3(F_2).
```

It follows that `F cap L=G_Q`, while every nonidentity tail element has
nontrivial symbol. In particular the constant Weyl element `u` has the
nonidentity constant Weyl symbol and is not finitary.

Substituting `S->z`, `T->z^(-1)`, and `Q->0` in `a` and `h` gives the
two displayed symbols in the claim. Every element of `H=<L,a>` has symbol
a power of `diag(z,z^(-1),1)`, hence has diagonal symbol. Both `u` and `h`
have nondiagonal symbols, so neither belongs to `H`; since `u in F`,
neither `F` nor `<F,h>` is contained in `H`.

Finally `F` contains every constant root on these three coordinates and
`a=h u`. The second prerequisite therefore gives
`EL_3(J)=<a,EL_3(F_2)><=<F,h><=EL_3(J)`.

The invalidated route explicitly uses `F<=L` and `u in L` to apply the
LEF theorem for `H` to `<F,h>`. The symbol calculations disprove those
premises, so that route is unusable. They say nothing against a different
finite-model construction for the two particular cells.
