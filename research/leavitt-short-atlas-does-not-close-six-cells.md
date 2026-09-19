---
rg: 2
id: leavitt-short-atlas-does-not-close-six-cells
kind: claim
title: No shortest Steinberg relation among the three mixed Leavitt coefficients closes a six-cell picture
artifacts:
  - research/artifacts/leavitt-three-gate-short-coefficient-atlas-2026-08-21.md
  - research/artifacts/enumerate-leavitt-three-gate-six-cell-pictures.py
distinct_from:
  leavitt-three-gate-square-picture-area-eight: that reduces coefficient words using only three originally selected involution gates; this adds every shortest exact coefficient relation visible from the mixed labels and proves that none closes area six.
  leavitt-length-six-three-gate-weight-survivor: that proves generation and failure of the weight test but does not classify low-area coefficient regions.
---

For

```text
h_0=a_0,  h_1=q_0p_1,  h_2=e_0,
k_0=a_1,  k_1=q_1,     k_2=p_0e_1
```

in the coefficient free product `G_0*G_1`, the complete shortest atlas
forced directly by root support is

```text
h_0^2=h_2^2=k_0^2=k_1^2=1,
[h_0,h_2]=[k_0,k_1]=1.                                  (SCA1)
```

The other two mixed labels `h_1` and `k_2` are cyclically reduced
two-syllable free-product words, hence have infinite order.

Re-reducing the complete six-cell ribbon census by `(SCA1)` produces no
coefficient-boundary disk.  In the closest cases, four internal regions
would be trivial except for one of the three cyclic rotations of

```text
h_0 h_1^(-1) h_2 h_1.                                   (SCA2)
```

But `(SCA2)` is nontrivial in `G_0*G_1`.  Therefore no shortest
Steinberg/root-commutator relation involving the three mixed labels closes
a reduced picture with at most six faces.

This strengthens the area-eight screen honestly: an actual six-face kernel
picture, if one exists, must use a genuinely longer coefficient identity,
not an omitted involution or commuting-root relation.  It does not yet rule
out simultaneous longer identities in several internal regions.
