---
rg: 2
id: bounded-period-compressors-no-defect-route
kind: route
title: Bounded cluster period plus ambient-decomposition Kun--Thom kills the compression defect
target: bounded-period-compressors-carry-no-sofic-defect
requires:
  - bounded-cluster-period-preserves-kazhdan-fixed-algebras
  - ambient-decomposition-kun-thom-normalization
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**Item 1.** Let `u` be tame, as witnessed by `sigma`, a cluster frame of `sigma|_L`, and
`p`. Put `H = <L, u>`, a finitely generated group in which `L` is infranormal.
- The restriction `sigma|_H` is a sofic representation of `H`.
- By item 2 of `bounded-cluster-period-preserves-kazhdan-fixed-algebras`, the
  `(S ∪ {u})`-generator graph of `sigma|_H` is expander-decomposable after
  `o_U(|Y_n|)` edge changes.
- `ambient-decomposition-kun-thom-normalization` (KT\*), with `Gamma = L` and `T = S ∪ {u}`,
  then says that `sigma(u)` normalizes `C_(S_U)(sigma(L))`.

Now let `c ∈ C_G(L)`. Then `sigma(c) ∈ C_(S_U)(sigma(L))`, so
`sigma(u c u^-1) ∈ C_(S_U)(sigma(L))`, and `sigma([u c u^-1, l]) = 1` for every `l ∈ L`.
A sofic representation in the sense of Kun--Thom Definition 2.1 has
`tr sigma(g) = 0 != 1 = tr sigma(1)` for `g != 1`, so it is injective. Hence
`[u c u^-1, l] = 1`.

**Item 2.** Every normal generator of `D_G(L)` in (ICD1) is trivial by item 1.

**Item 3.** Assume `D_G(L) = K != 1`. Some generator `[u c u^-1, l]` is nontrivial, so its
`u` is wild by item 1.
- *Unbounded period.* Wildness means that for every sofic representation, every cluster
  frame and every `p`, `BP_p` fails.
- *Infinite dimension.* By items 3 and 5 of the fixed-algebra node, if some
  `D_U^(sigma(L))` were finite-dimensional, then its frame would satisfy some `FD_k`, and
  hence `BP_k`. So every `D_U^(sigma(L))` is infinite-dimensional.

`G` is sofic, so sofic representations exist. The closed-source reduction is (GC3) of
`compression-defects-grow-under-centralizer-closure`.
