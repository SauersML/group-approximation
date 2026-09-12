---
rg: 2
id: spherical-one-overlap-forest-rounding-proof
kind: route
title: Start each component with one relation and attach the rest one shared map at a time
target: spherical-one-overlap-forest-rounding
requires:
  - spherical-single-relation-near-perfect-packing
  - spherical-one-shared-map-relation-extension
  - partial-schreier-completion-preserves-sofic-loss
  - trace-separation-sphere-distance-concentration
---

There are only finitely many relations.  Fix a small radius `rho>0`, to be
sent to zero after the finite table is fixed.  Start each component with
`spherical-single-relation-near-perfect-packing`; this supplies the three
label maps on `1-o(1)` of the cloud and makes the first relation exact there.

Attach subsequent relations in the assumed order.  Exactly one label map is
already present.  Apply `spherical-one-shared-map-relation-extension`: choose
one new label by a radius-`rho` near-perfect matching and define the third map
by exact composition.  If the old map has geometric error `e`, the forced new
map has error at most `e+2rho` off another `o(N)` exceptional set.  Hence after
at most `R` relation attachments every map has pointwise geometric error at
most `O(R rho)` on `1-o(1)` of its domain.  Since `R` is fixed, choose `rho`
so small that this bound is below any desired fixed separation threshold.
The union of all domain/range losses and all pointwise relation-defect
exceptional sets is still `o(N)`.

It remains to check regular separation.  For distinct table labels `u != v`,
regular-character trace separation and
`trace-separation-sphere-distance-concentration` imply that, outside `o(N)`
roots, the two unitary image points `U_u x_i` and `U_v x_i` are separated by
a fixed positive Euclidean distance (indeed their squared distance is close
to `2`).  With `rho` chosen so that both partial-map tracking errors sum to
less than half that distance, equality

```text
sigma_u(i)=sigma_v(i)
```

is impossible on every such common-domain root.  Thus the partial maps are
Hamming-separated on `1-o(1)` of the cloud.

Finally apply `partial-schreier-completion-preserves-sofic-loss` to extend
all partial bijections to permutations.  Since the table is fixed, the added
Hamming loss is `o(1)`, while all listed exact partial relations and label
separation survive asymptotically.
