---
rg: 2
id: openai-bounded-median-component-matching-proof
kind: route
title: Normalize by a bounded median, then convert zero drift into concentration by coarea and expansion
target: openai-bounded-median-component-matching
requires: [kun-expander-decomposition-formalized]
artifacts:
  - official/counterexample.tex
  - official/reasoning.tex
---

## Why sufficient

The prerequisite supplies both partitions: applied to the restricted
approximation of `Gamma` on `S_Gamma` it gives the `Gamma`-components, and
applied to the approximation of `G` on `S_G` it gives the ambient components,
each a `gamma`-expander after an `o(N)` edit of the edge set.  Everything else
in the target is elementary once those two objects exist.

**Step 1, transport.** `t_i Gamma t_i^(-1) <= Gamma` says a `Gamma`-word acts
on `p_i(C)` as the `p_i`-conjugate of a `Gamma`-word.  Expansion of the target
`Gamma`-component then forces `p_i(C)` to lie almost entirely inside a single
one, `D`, apart from components carrying `o(N)` vertices in total: a set
meeting two components in comparable proportions has a boundary the expansion
constant forbids.  This is where the argument would stop without a size
comparison -- two different transported components may still choose the same
`D`.

**Step 2, the normalization.** `f = M/(M + m_A)` is bounded, strictly
increasing in `M`, and has median `1/2` on `A` by the choice of `m_A`.  The
inequality `(1-eta)x/((1-eta)x+a) >= x/(x+a) - eta` turns the one-sided size
estimate of Step 1 into `f(sz) >= f(z) - eta_n` off `o(N)` vertices.  The
choice of a bounded function is the whole point: `M` itself has unbounded
ratios across components and no averaging argument survives them.

**Step 3, zero drift.** Every generator acts by a permutation, so the total
increase of `f` equals its total decrease; with an `o(N)` pointwise deficit
and `f` bounded, both are `o(N)`, and the edge sum
`sum |f(z) - f(y)|` over the edited ambient graph is `o(N)`.

**Step 4, coarea and expansion.** The finite coarea identity is exact for any
`f` and any finite graph.  Applying the expansion of `A` to the smaller side
of each superlevel cut, and splitting at the median so that each side is the
smaller one on its own range, gives
`gamma_G sum_A |f - 1/2| <= sum_(E(A)) |f(z)-f(y)| = o(N)`.  Markov's
inequality then removes `o(N)` vertices and leaves `|f - 1/2| <= delta_n`.
Inverting `f` bounds the size ratio by `rho_n = ((1+2delta_n)/(1-2delta_n))^2`.

**Step 5, injectivity.** By Step 4, `|p_i(C)| = |C|(1 + o(1))` and
`|D| = |C|(1 + o(1))`, so `p_i(C)` fills more than half of `D` for large `n`.
Transported components are images of disjoint sets under one permutation,
hence disjoint, so no two of them can each fill more than half of the same
`D`.

## Why this route asserts more than a reading of the source

The same conclusion is reached in Lean here, from the same prerequisite, in
`Criterion/LocalCriterion` and `Criterion/SelectionOutput`.  Reading the
chapter's proof is therefore not the only evidence for this node: the
statement has been proved in a machine-checked development that did not have
the chapter's proof in front of it.
