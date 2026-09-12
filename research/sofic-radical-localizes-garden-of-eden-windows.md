---
rg: 2
id: sofic-radical-localizes-garden-of-eden-windows
kind: claim
title: Every Garden-of-Eden window of an injective automaton contains two cells differing by a sofic-invisible element
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that forbids a surjunctive cover matching the decoder-encoder product rectangle; this forbids an almost-multiplicative permutation model, with collisions allowed, that separates the cells of a Garden-of-Eden window, and names the normal subgroup where the window must fold.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `G` be a countable group and `A` a finite alphabet with `|A| >= 2`. Define
the **sofic radical** `Rad(G)` as the set of `g` such that for every `eps>0`
there are a finite `F` containing `g` and `delta>0` with
`d(phi(g), id) <= eps` for every map `phi: F -> Sym(V)`, `V` finite, satisfying
`phi(1)=id` and `d(phi(a)phi(b), phi(ab)) <= delta` for `a,b,ab` in `F`. Here
`d` is normalized Hamming distance, and no freeness is required. `Rad(G)` is a
normal subgroup, and it is trivial exactly when `G` is sofic. It is the same
subgroup as `Rad_sof(G)` of `sofic-radical-soficization`, the kernel of
soficization: a homomorphism into a metric ultraproduct of symmetric groups has
a sofic image, and a sofic quotient embeds into such an ultraproduct. For
finitely presented groups, `sofic-radical-linear-action-criterion` gives the
equivalent linear displacement test.

**Theorem.** Let `tau` be an injective cellular automaton over `G` with memory
`M`, and `p in A^Omega` a Garden-of-Eden pattern. Then `Omega^-1 Omega`
contains a nontrivial element of `Rad(<M>)`, which is contained in `Rad(G)`.
In particular no Garden of Eden has a single cell.

The proof runs the Gromov--Weiss counting along almost-multiplicative models.
Collisions only help the decoding count, so they are allowed. A disjoint union
and a product amplification then produce models in which every difference
`k^-1 k'` of the window moves at density near one. If no such difference were
invisible, injective charts of the window would have density at least `1/2`,
and the counting would contradict injectivity. Full proof: Section 1 of the
linked artifact.

This is exactly the step of the Gromov--Weiss proof that fails for a strict
automaton. Two cells of every Garden-of-Eden window must be folded together by
every permutation model of the memory group. Over a sofic memory group nothing
folds, so the theorem recovers surjunctivity there.
