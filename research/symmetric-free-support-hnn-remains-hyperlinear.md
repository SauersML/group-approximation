---
rg: 2
id: symmetric-free-support-hnn-remains-hyperlinear
kind: claim
title: Symmetrically gluing two free-phase support factors by HNN remains hyperlinear
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that uses residual finiteness for finite associated subgroups; this treats the first natural infinite associated subgroups supplied by the free-phase support calculation.
  ascending-hnn-cannot-create-nonhyperlinearity: that treats an injective endomorphism of the whole base; this is a nonascending HNN extension identifying two proper free direct factors.
---

Let `L_0,L_1` be two copies of a finite direct product `L` of finite-rank
free groups (in particular, `L` is a right-angled Artin group), and let

```text
E=<L_0 times L_1,t | t ell_0 t^(-1)=ell_1, ell in L>,    (SFH1)
```

where the displayed correspondence is the fixed basis isomorphism.  Then
`E` is hyperlinear.  More generally, if a hyperlinear group `G_0` commutes
with both factors and the stable letter fixes `G_0`, the corresponding HNN
extension is `G_0 times E` and is hyperlinear.

Indeed, for `L_n=t^n L_0t^(-n)`, the height kernel is the graph product of
the copies `(L_n)_(n in Z)` with exactly the relations

```text
[L_n,L_(n+1)]=1.                                         (SFH2)
```

Every finite interval in this graph product is again a right-angled Artin
group.  The full kernel is their directed union and is hyperlinear.  The
quotient is `Z`, so hyperlinear-by-amenable extension permanence makes `E`
hyperlinear.

Thus identifying the two structurally identical proper support groups from
`(FPS4)`, or equal-length products of such factors along two join-tree
branches, does not supply the missing chord mechanism.  The infinite edge
must couple the support factors asymmetrically, impose additional holonomy,
or otherwise avoid the path-RAAG height kernel.
