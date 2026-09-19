---
rg: 2
id: near-trivial-torus-characters-track-the-moving-kernel
kind: claim
title: Near-trivial torus characters track the moving kernel rather than create a Green blowup
distinct_from:
  right-u-reynolds-has-torus-hecke-blocks: that writes the character blocks as weighted Mobius matrices; this rules out the naive perturbative use of characters approaching the trivial block.
  proper-torus-reynolds-is-edge-refinement: that isolates the fiber-mean-zero target geometrically; this proves that mere continuity from the fiber-constant kernel does not produce its required divergent mode.
---

**ESTABLISHED; LOCAL PERTURBATION NO-GO.**  Let `C_t:E->F` be a
continuous finite-dimensional family of Hilbert-space operators for
`|t|<epsilon`.  Assume its rank is locally constant and that

```text
||C_0 x||_2 >= sigma ||x||_2
       for x in ker(C_0)^perp                           (NTK1)
```

with `sigma>0`.  Let `P_t` be the orthogonal projection onto
`ker(C_t)^perp`.  After shrinking `epsilon`, the smallest nonzero singular
value of `C_t` is at least `sigma/2`.  Therefore, for every
`v in ker(C_0)`,

```text
||(P_t v)||_2
 <=(2/sigma)||(C_t-C_0)v||_2.                          (NTK2)
```

Indeed `v-P_t v` lies in `ker(C_t)`, so

```text
C_t P_t v=C_t v=(C_t-C_0)v.
```

Apply the lower singular-value bound on `ker(C_t)^perp` to obtain
`(NTK2)`.

More decisively, if `P_t v` is nonzero and

```text
w_t=P_t v/||P_t v||_2,
```

then

```text
||C_t w_t||_2 >= sigma/2.                              (NTK3)
```

Thus a vector from the exact kernel at the trivial character does not turn
into a normalized near-kernel merely because the character phases approach
one.  Its transverse Moore--Penrose component shrinks at the same order as
the raw residual, and normalization restores the nonzero singular gap.

Apply this to any fixed proper-torus Fourier matrix `C_(G,theta)` from
`right-u-reynolds-has-torus-hecke-blocks`, with `t` a local character-phase
parameter near the trivial character.  As long as rank is constant, the
gradient kernel of the trivial multipartite block follows the moving exact
kernel by `(NTK2)` and cannot supply the divergent ratio sought in `(RUB8)`.
At a rank jump the statement applies separately on each constant-rank
stratum and makes no assertion across the jump.

This is an `L2` perturbation statement and does not prove a uniform
`l_infinity` Green bound in a growing family.  It identifies what a genuine
counterexample must add: dimension-dependent `l_infinity/L2` geometry, a
macroscopic component transverse to the moving kernel, or a nonperturbative
rank-changing block.  Near-trivial character phases alone are not such a
construction.

