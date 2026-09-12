---
rg: 2
id: graph-folds-over-surjunctive-groups-are-surjunctive
kind: claim
title: A graph of groups mapping faithfully on vertex groups to a surjunctive group is surjunctive
distinct_from:
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that treats direct-sum lamp kernels; this treats arbitrary graph-of-groups fundamental groups with a homomorphism to a surjunctive host injective on every vertex group, through a free graph kernel.
artifacts:
  - research/artifacts/surjunctivity-graph-folds-2026-09-11.md
---

Let `P` be the fundamental group of any connected graph of groups with
injective edge maps. If there is a homomorphism `f:P->G` to a surjunctive
group whose restriction to each vertex group is injective, then `P` is
surjunctive.

No finite generation, residual finiteness, amenability, separability, or
soficity condition is imposed on the edge groups. The map need not be
injective on `P` or surjective onto `G`.

In particular, for subgroups `A,B<=G` and `C<=A intersection B`, the
amalgam `A *_C B` is surjunctive. An HNN extension of `A<=G` is
surjunctive when its prescribed associated-subgroup isomorphism is
conjugation by a specified element of `G`.

The proof enlarges each vertex group to `G` without creating new reduced
word pinches. The fold kernel of the resulting split extension is the
fundamental group of a graph whose vertices are all fixed by `G`. Finite
edge deletion gives the required finitary structure, including the
translated spanning-tree correction terms.

This extends the preexisting double-group argument. It does not establish
arbitrary HNN or amalgam closure, arbitrary free-by-surjunctive closure,
or the universal Gottschalk conjecture.
