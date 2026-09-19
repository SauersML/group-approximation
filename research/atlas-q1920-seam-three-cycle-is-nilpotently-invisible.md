---
rg: 2
id: atlas-q1920-seam-three-cycle-is-nilpotently-invisible
kind: claim
title: The Q1920 seam three-cycle lies in every lower-central term of the universal kernel
artifacts:
  - experiments/atlas_a4_q1920_kernel_homology.g
  - research/artifacts/atlas-a4-q1920-seam-kernel-homology.json
distinct_from:
  atlas-q1920-universal-seam-splits-over-a5: that computes the first homology and split A5 quotient; this identifies the exact residual layer in which a surviving seam three-cycle must live.
---

Use the universal seam notation

```text
P = N semidirect A5,       N_ab ~= C2^9,
```

and let `z` be the first-packet element with `z^3=1`.  For every `k>=2`, the
quotient `N/gamma_k(N)` is a finitely generated nilpotent group whose
abelianization is a quotient of `C2^9`.  A finitely generated nilpotent group
with finite abelianization is finite.  Moreover, if its abelianization is a
2-group then the group itself is a 2-group: any nontrivial odd Sylow subgroup
would have a nontrivial odd-order abelian quotient.

It follows that the image of `z` in every `N/gamma_k(N)` is trivial.  Hence

```text
z in intersection_{k>=2} gamma_k(N),
z in gamma_3(N)=[N',N].                                  (Q1920-NIL-1)
```

The statement permits `z=1` in the universal group; what matters for the
packet problem is its consequence in any quotient that preserves the labeled
first-packet `S3`.  There `z` has order three and survives inside the
nilpotent residual of the image of `N`.  In particular its class in

```text
N'/[N',N]
```

is zero, and no nilpotent or purely 2-local kernel can give a faithful finite
completion.

## Attempts

Computing the class-two quotient or the `A5`-module `N'/[N',N]` cannot locate
the required three-torsion: `(Q1920-NIL-1)` proves that this layer kills it
before any calculation.  Ordinary extension cohomology with coefficients in
`N_ab` also cannot obstruct the universal group, because `P=N semidirect A5`
is already split.  A viable next invariant must see the nonnilpotent residual,
for example the finite residual or a nonnilpotent solvable quotient retaining
`z`.
