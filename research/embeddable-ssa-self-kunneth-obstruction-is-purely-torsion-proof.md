---
rg: 2
id: embeddable-ssa-self-kunneth-obstruction-is-purely-torsion-proof
kind: route
title: Rationalize the split external product after the absorption computation
target: embeddable-ssa-self-kunneth-obstruction-is-purely-torsion
requires:
  - ssa-self-kunneth-exact-k-theory-criterion
  - ssa-qoinfty-absorption-forces-rational-k-profile
---

Put `G=K_*(D)`. The rational-profile theorem gives

```text
G tensor Q ~= (Q,0),       [1_D] |-> 1.                (1)
```

Strong self-absorption identifies `K_*(D tensor D)` with `G` by the
first-factor embedding. Under `(1)`, the rationalization of the external
product is therefore

```text
Q tensor_Q Q -> Q,       r tensor s |-> rs,            (2)
```

which is an isomorphism. Since localization at the nonzero integers is flat,

```text
ker(alpha) tensor Q = ker(alpha tensor Q)=0.
```

An abelian group has zero rationalization exactly when it is torsion, so
`ker(alpha)` is torsion. The exact criterion also makes `alpha`
split-surjective, so this kernel is a direct summand; `(1)` makes `K_1(D)`
torsion. Finally every
`Tor_1^Z` group is torsion. The exact criterion says these are the only two
places where self-Kunneth can fail. QED
