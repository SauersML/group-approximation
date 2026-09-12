---
rg: 2
id: jacobson-head-root-from-locally-finite-collapse
kind: route
title: Kill the Jacobson head root by locally finite collapse inside the compression defect
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires:
  - locally-finite-defect-subgroup-dies-in-every-corona
  - binary-jacobson-mf-radical-dichotomy
---

Write `J=F_2<S,T | TS=1>`, `Q=1-ST`, `E=EL_5(J)`, and let

```text
L=GL_fin(N x {1,...,5},F_2)
```

be the finitary symbol kernel of `binary-jacobson-mf-radical-dichotomy`.
Three inputs assemble the target.

**The head root lies in the compression defect.**  Apply the rank-four
compression cell of `non_mf_groups_exist.tex` to the ring `J` with the pair
`S,T`: it produces `u` compressing `Lambda=EL_3(J)` and `c` centralizing
`Lambda` with

```text
[u c u^(-1), x_23(1)] = x_13(Q).
```

Extending by the identity on the fifth coordinate places `u` and `c` in
`E`, so `x_13(Q) in D_E(Lambda)`.  The ring `J` is finitely generated, so
`Lambda` has property (T) by Ershov-Jaikin-Zapirain.

**The symbol kernel is locally finite.**  Since `TS=1` and the
characteristic is two, the elements `f_(ij)=S^i Q T^j` satisfy
`f_(ij) f_(kl) = delta_(jk) f_(il)`, so they are matrix units spanning the
ideal `JQJ` over `F_2`; the span of those with `i,j<N` is a finite subring.
Hence `L` is the directed union of the finite groups it contains, and it is
normal in `E` as the kernel of the symbol map.  Also `Q` maps to
`1-z z^(-1)=0`, so `x_13(Q) in L`.

**Collapse.**  Apply `locally-finite-defect-subgroup-dies-in-every-corona`
with `G=E`, the property (T) subgroup `Lambda`, the compressor `u`, and
`A=L`.  Every homomorphism from `E` to an MF group is then trivial on `L`,
and in particular kills `x_13(Q)`, which is the target.

The dichotomy claim is what identifies `L` with the finitary group and
supplies exactness of the symbol sequence; with the target established it
also upgrades to the exact computation `Rad_MF(E)=L`.
