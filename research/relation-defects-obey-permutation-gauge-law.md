---
rg: 2
id: relation-defects-obey-permutation-gauge-law
kind: claim
title: Relation-defect permutations obey an exact nonabelian source-gauge cocycle law
distinct_from:
  spherical-one-shared-map-relation-extension: that theorem defines a previously unchosen map to force one relation; this identity describes how an already chosen whole permutation table's relation holonomies transform when every label is corrected on its source.
artifacts:
  - research/artifacts/hyperlinear-cycle-synchronization-bypasses-2026-08-21.md
---

Let `sigma_s` be permutations of one set and, for a tested relation `gh=k`,
define its defect permutation

```text
delta_(g,h,k) = sigma_k^(-1) sigma_g sigma_h.           (PGL1)
```

For arbitrary source corrections `c_s`, put

```text
tilde_sigma_s = sigma_s c_s.                            (PGL2)
```

Then the corrected relation defect is exactly

```text
tilde_delta_(g,h,k)
 = c_k^(-1) delta_(g,h,k)
   (sigma_h^(-1) c_g sigma_h) c_h.                     (PGL3)
```

In particular the corrected relation is exact precisely when

```text
c_k = delta_(g,h,k)
      (sigma_h^(-1) c_g sigma_h) c_h.                  (PGL4)
```

Thus simultaneous cycle synchronization can be formulated as a finite
nonabelian cocycle-trivialization problem for the relation holonomies, with
conjugation action supplied by the already chosen label permutations.