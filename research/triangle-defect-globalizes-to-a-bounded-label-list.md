---
rg: 2
id: triangle-defect-globalizes-to-a-bounded-label-list
kind: claim
title: A small affine orientation defect yields a dimension-free set of candidate labels hitting a constant fraction of heavy cosets
distinct_from:
  affine-orientation-triangle-defect-is-small: that is the analytic estimate producing a small defect; this consumes a small defect and produces the global list, and it is combinatorial rather than analytic.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  The globalization half of `affine-orientation-glue-lemma`:

```text
small triangle-defect probability  ==>  a set Q with |Q| <= L and
                                        Pr_{b in B}[C_b intersect Q != empty] >= gamma,
```

with `L` and `gamma` independent of `k`.

This is a local-consistency-implies-global-structure statement of a
familiar shape: the star configurations of
`affine-orientation-triangle-defect-is-small` say that chosen coset
representatives agree on almost every affine plane, and the conclusion asks
for a bounded set of points explaining a constant fraction of the choices.
Nothing in it is analytic; the input is a combinatorial density statement
about `F_2^k` and the output is a bounded hitting set.

**A caveat that must not be lost.**  The dossier that opened this region
credits "the Cairn machinery" with supplying this step.  Cairn is this
repository's build system for unknown facts -- a bookkeeping graph over
claims and routes.  It is not a mathematical method, and there is no
theorem of Cairn's that converts local defect into global structure.  The
step is an ordinary open problem, recorded as one.

## Attempts

* **Almost-cocycle to cocycle.**  Treat `b |-> q_b` as an almost-cocycle on
  `F_2^k` and try to correct it to an exact one, then read `Q` off the
  corrected object.  Where it dies: the values `q_b` are coset
  *representatives*, so the natural target group is `Omega/<b>` and varies
  with `b`; there is no single group in which the cocycle equation lives,
  and the usual stability arguments assume a fixed target.
* **Density increment on planes.**  Iterate: find a plane with many stars,
  restrict, repeat.  Where it dies: the increments are on the direction set
  `B`, but the conclusion is about points of `Omega`, and the two are not
  linked by the iteration -- one can drive `B` to a subspace while the
  representatives stay spread.
* **Bounded-list extraction from pairwise agreement.**  A sunflower or
  regularity argument on the family `{C_b}`.  Where it dies: `|C_b| = 2`,
  so pairwise intersections are single points and the family carries almost
  no combinatorial structure without the defect bound doing real work; the
  step where the defect enters is unidentified.
