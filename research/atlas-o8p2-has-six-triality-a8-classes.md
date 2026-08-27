---
rg: 2
id: atlas-o8p2-has-six-triality-a8-classes
kind: claim
title: O8+(2) has six A8 classes, three natural self-normalized and three orthogonal S8-normalized
artifacts:
  - experiments/atlas_o8p2_affine_complement_fusion.py
  - experiments/atlas-o8p2-affine-complement-fusion.json
  - experiments/atlas_o8p2_triality_affine_fusion.py
  - experiments/atlas-o8p2-triality-affine-fusion.json
distinct_from:
  atlas-o8p2-carrier-a8-classes-and-absorption: that gives two complement classes locally in each affine carrier; this computes their ambient fusion and identifies every natural and orthogonal carrier class.
---

The six local complement classes supplied by the three triality classes of
`2^6:A8` are pairwise nonconjugate in `G=O8+(2)`.  They are all the `A8`
classes of `G`.  Three have ambient normalizer `A8` and three have ambient
normalizer `S8`:

```text
three classes: |N_G(A)|=20160, |A^G|=8640;
three classes: |N_G(A)|=40320, |A^G|=4320.           (O8F1)
```

The three natural `A8<A9` carrier classes fuse bijectively to the three
self-normalized classes in the first line.  The three orthogonal
`A8<S6(2)` carrier classes fuse bijectively to the three `S8`-normalized
classes in the second line.  Together they cover all six affine complement
classes, so the maximal-carrier fork contains no seventh ambient `A8` class.
Triality permutes the three natural classes and separately the three
orthogonal classes; it does not fuse them inside `G`.

In one fixed `2^6:A8` maximal-class action of degree 135, the self-normalized
class lies in one carrier of that class, whereas the `S8`-normalized class
lies in two.  The incidence identities

```text
135*64 = 8640*1,       135*64 = 4320*2              (O8F2)
```

independently check both normalizer branches.

Consequently the same-carrier exclusions already remove a proper subset of
the equality cells: pairs sharing an `A9` are natural-support cells, and
pairs sharing an `S6(2)` are calibrated orthogonal cells.  The remaining
packet screen must be indexed by ordered pairs among these six ambient
classes together with their double cosets, after deleting precisely those
absorbed incidences.  It must not treat the two affine complement types as a
single class.

