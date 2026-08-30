---
rg: 2
id: higher-whitehead-universal-group-via-the-two-hnn-edges
kind: route
title: Re-read both universal-host HNN steps on every homotopy group
target: higher-whitehead-universal-finitely-presented-torsion-free-group
requires: [whitehead-universal-finitely-presented-torsion-free-group, waldhausen-hnn-vertex-higher-whitehead-injectivity, waldhausen-free-double-whitehead-space-contractible]
---

Take the explicit witness constructed in
[[whitehead-universal-group-via-effective-hnn-and-rope]].

For a countably generated recursively presented torsion-free `K`, its
inclusion as a free factor of the universal free product `Q` is split by a
group retraction. The inclusion

```text
Q -> V=Q*F(a,b)
```

is also split. Proposition 15.3 of Waldhausen makes the Whitehead-space
construction natural in the group, so both maps are split-injective on every
homotopy group.

The next map `V->E` is the vertex inclusion in the effective
two-generator HNN extension. Its edge group `A` is free, possibly of
countably infinite rank. Theorems 19.4 and 19.5(1) make `Wh_Z(A)`
contractible; equivalently, use its filtering union of finite-rank free
factors and Waldhausen's direct-limit continuity. Hence
[[waldhausen-hnn-vertex-higher-whitehead-injectivity]] injects every
`Wh_i(V)->Wh_i(E)`.

For the last step, use the actual Higman-rope construction rather than only
its ordinary-Whitehead corollary. It first includes `E` as the split factor

```text
E -> P x E
```

and then forms an HNN extension whose edge is the free-group double

```text
L=F *_R F.
```

The whole space `Wh_Z(L)` is contractible by
[[waldhausen-free-double-whitehead-space-contractible]]. The split map
followed by the HNN vertex map therefore injects every `Wh_i`. The same
existing rope argument proves that the final group `U` is finitely
presented and torsion-free.

Composing these split and HNN injections proves the assertion for every
`i>=0` with one and the same embedding `K->U`. QED
