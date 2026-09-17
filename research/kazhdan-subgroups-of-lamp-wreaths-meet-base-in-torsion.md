---
rg: 2
id: kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion
kind: claim
title: A Kazhdan subgroup of an abelian-lamp wreath product meets the lamp group only in torsion
distinct_from:
  kazhdan-rational-relation-cover-reduction: that embeds the torsion-free cover into a wreath product to make it sofic; this proves that a Kazhdan subgroup of such a wreath product cannot meet the torsion-free lamps at all, so the embedding only ever sees the quotient.
  abelian-lamp-mf-classification: that classifies MF-ness of abelian lamps over compressed Kazhdan site spaces; this is about property (T) of subgroups of the wreath product, not about MF approximations of the lamps.
  free-abelianized-cover-is-torsion-free: that builds torsion-free covers with free abelian kernels inside Z^n wr Q; this shows that no Kazhdan subgroup of such a cover meets that kernel.
  relation-cover-sofic-envelope-forces-trivial-kernel: that is the consequence for the relation-cover route; this is the general wreath-product statement.
artifacts:
  - research/kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion-proof.md
---

**ESTABLISHED.**  Let `W` be a countable abelian group, `Q` a countable group
and `X` a countable `Q`-set. Put

```text
B = (+)_{x in X} W,        G = W wr_X Q = B semidirect Q,          (LW1)
```

where `Q` permutes coordinates. Let `K <= G` be a subgroup with property (T).
Then every element of `K cap B` has finite order.

In particular:

1. If `W` is torsion-free, then `K cap B = 1`, so the projection `G -> Q` is
   injective on `K`. Every Kazhdan subgroup of `W wr_X Q` is isomorphic to a
   subgroup of `Q`.
2. More generally, if `M` is a torsion-free abelian group, `Q` acts on `M`, and
   `M` embeds `Q`-equivariantly into some `(+)_X W`, then every Kazhdan
   subgroup of `M semidirect Q` maps injectively to `Q`.

**The invariant and the step where every member dies.** The dual `B^` carries
the `Q`-invariant product measures `mu_n = nu_n^(x)X`, with `nu_n` normalized
Haar measure on shrinking neighbourhoods of `0` in `W^`. On `L^2(B^, mu_n)`, the
group `B` acts by multiplication by characters and `Q` by translation. The
constant function is asymptotically `G`-invariant. Property (T) of `K` gives a
nonzero `K`-invariant vector, and an invariant vector is supported on the
annihilator of `K cap B`. If `K cap B` contains an element of infinite order,
that annihilator has `mu_n`-measure zero. So any construction that puts a
Kazhdan group into a lamp wreath product with its infinite-order lamp part
nonzero dies at that last step.

**Calibration.** `Z^3 semidirect SL_3(Z)` is Kazhdan with nonzero abelian
kernel. This is consistent. The image of `Z^3` in `(+)_X W` would be finitely
generated, so its total support would be a finite `Q`-invariant subset of `X`.
Then a finite-index subgroup of `SL_3(Z)` would fix that subset pointwise and
act trivially on the image, while it acts faithfully on `Z^3`. So no
equivariant embedding exists. The finite-lamp case is excluded for a reason: when `W` is finite,
`W^` is discrete and `nu_n` cannot shrink to `0` without becoming the Dirac
mass.

Proof: route `kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion-proof`.
