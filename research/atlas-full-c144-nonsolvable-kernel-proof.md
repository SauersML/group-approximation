---
rg: 2
id: atlas-full-c144-nonsolvable-kernel-proof
kind: route
title: Quotient the last forward cube by the reduced-seam kernel
target: atlas-full-c144-relation-forces-nonsolvable-q1920-kernel
requires:
  - atlas-q1920-universal-seam-splits-over-a5
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/verify_atlas_full_c144_nonsolvable_kernel.py
  - experiments/atlas_a4_q1920_module_structure.g
  - research/artifacts/atlas-a4-q1920-module-structure.json
  - experiments/atlas_a4_q1920_kernel_homology.g
  - research/artifacts/atlas-a4-q1920-seam-kernel-homology.json
---

Let `P=N semidirect A5` be the reduced seam and let `G` be a quotient
obtained after imposing the last forward relation `(z b)^3=1`.  Assume that
the marked subgroup `Q=2^5:A5` remains embedded in `G`, and write `K` for
the image of `N`.  The reduced-seam theorem gives

```text
V,z <= K,             V ~= C2^5.                         (C144N-1)
```

Because `K` is normal in `G`, its intersection with `Q` is normal in `Q`.
The exact normal-subgroup lattice of the marked `Q` has no subgroup strictly
between `V` and `Q`, so

```text
K cap Q = V  or  Q.                                     (C144N-2)
```

Suppose that `K` is solvable.  It cannot contain the perfect nonsolvable
group `Q`; hence `(C144N-2)` gives `K cap Q=V`.  The radial subgroup
`B=<y,b>~=S3` intersects `V` trivially, so the marked involution `b` does
not lie in `K`.  Thus `bK` is a nonidentity involution in `G/K`.

On the other hand, `z in K`, and the last forward cube projects to

```text
(bK)^3=(z b K)^3=K.                                    (C144N-3)
```

An element whose order divides both two and three is the identity.  Hence
`bK=K`, contradicting `b notin K`.  Therefore `K` is nonsolvable.  The
argument uses no finiteness assumption on `G` and applies to both exact
marked `Q1920` classes.
