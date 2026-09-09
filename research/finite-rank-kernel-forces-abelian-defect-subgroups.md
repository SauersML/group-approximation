---
rg: 2
id: finite-rank-kernel-forces-abelian-defect-subgroups
kind: claim
title: A finite-rank normal kernel with locally residually finite quotient makes every finitely generated normal defect subgroup abelian, free in characteristic zero
distinct_from:
  locally-residually-finite-targets-kill-compression-defects: that is the target-side lemma consumed here for the quotient step; this is a structure theorem for normal subgroups of the defect inside a faithful linear group with a finite-rank normal kernel.
  compression-defect-dies-in-finite-dimensions: that is the finite-dimensional sterility theorem, consumed here on the finite-dimensional total image space E; this is an infinite-dimensional statement whose conclusion is an additive embedding of the defect subgroup rather than its triviality.
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the positive theorem in positive characteristic, where the finite elementary abelian outcome here is exactly the finite central witness it consumes; this is the dichotomy explaining why characteristic zero admits no such witness.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `k` be a field, `V` a `k`-vector space of any
dimension, and `G <= GL_k(V)` a group acting faithfully.  Let `N <| G` be
a normal subgroup such that `a - I` has finite rank for every `a in N`,
and suppose `G/N` is locally residually finite.  Let `L <= G` be finitely
generated, and let

```text
K <| G,     K finitely generated,     K <= D_G(L),                 (FRK1)
```

with `D_G(L)` the compression--centralizer defect.  Put

```text
E = sum_(a in K) (a - I) V.                                         (FRK2)
```

Then `dim_k E < infinity`, `E` is `G`-invariant, and every `a in K`
restricts to the identity on `E`.  Consequently `(a - I)(b - I) = 0` for
all `a, b in K`, and

```text
K -> ( Hom_k(V/E, E), + ),     a |-> a - I                          (FRK3)
```

is an injective homomorphism of groups.  Hence:

* if `char k = 0`, `K` is free abelian of finite rank;
* if `char k = p > 0`, `K` is a finite elementary abelian `p`-group.

**Normal Kazhdan subgroups.**  In characteristic zero a normal Kazhdan
`K <= D_G(L)` is trivial: property (T) makes `K` finitely generated, an
infinite finitely generated abelian group surjects onto `Z` and so is not
Kazhdan, and `K` is torsion-free.  The same holds for any finitely
generated normal `K <= D_G(L)` with finite abelianization.  In
characteristic `p` the theorem allows a finite elementary abelian normal
Kazhdan subgroup and does not force it to vanish; that is the case the
torsion theorem exploits.

**Where finite generation is spent.**  Only in `dim E < infinity`.  For
any normal `K <= D_G(L)` whose total image space `(FRK2)` is finite
dimensional, `(FRK3)` is still an injective additive embedding.

**Where the hypotheses on `N` are spent.**  The locally residually finite
quotient absorbs the defect (`K <= N`); the finite-rank condition makes
`E` finite dimensional.  The target
`integral-jacobson-defect-has-no-normal-kazhdan-subgroup` is the instance
`V = Q^((N_0))`, `N` the symbol kernel, `G/N <= GL_n(Z[z,z^-1])`.

Derivation: `finite-rank-kernel-forces-abelian-defect-subgroups-proof`.
