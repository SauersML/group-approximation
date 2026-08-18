---
rg: 2
id: openai-bounded-median-component-matching
kind: claim
title: Bounded-median normalization matches transported expander components injectively
distinct_from:
  openai-expander-matching-criterion: That is the criterion, which also needs the selection of a component, the completion of partial permutations and the repair of expansion; this is the single analytic step inside it -- component sizes cannot drift inside one ambient expander -- and it concludes nothing about LEF.
  hs-expander-block-decomposition: That asks for a normalized-Hilbert-Schmidt analogue of the block decomposition and is open; this is a statement about permutation models and component sizes over the normalized Hamming distance, and it is proved.
  spectral-component-motion-bound: That bounds how far a compression can move a commuting-orbit witness across connected spectral components of an operator; this compares the SIZES of the components of two expander decompositions of the same finite model.
  one-sided-compression-nonsofic-criterion: That is the full formalized bridge from many expanders to one; this is the size-comparison step alone, stated as the chapter states it.
artifacts:
  - official/counterexample.tex
  - official/reasoning.tex
---

ESTABLISHED.  The analytic heart of [[openai-expander-matching-criterion]],
and the part worth stealing on its own.

Setting: a sofic approximation `p_n : G -> Sym(Y_n)` with `N = |Y_n| -> oo`,
decomposed twice by [[kun-expander-decomposition-formalized]] -- once on the
`Gamma`-generators, once on the `G`-generators.  For `z in Y`, let `C(z)` be
its `Gamma`-component and `M(z) = |C(z)|`.  For an ambient component `A`, let
`m_A` be a vertex-weighted median of `M` on `A`, and put

    f(z) = M(z) / (M(z) + m_A),   z in A.

Then `0 < f < 1` with median `1/2` on every `A`, and:

* **almost monotone.** `t_i Gamma t_i^(-1) <= Gamma` makes each transported
  component `p_i(C)` lie almost inside one `Gamma`-component, so
  `f(sz) >= f(z) - eta_n` off `o(N)` vertices for every positive ambient
  generator `s`, using the elementary inequality
  `(1-eta)x/((1-eta)x + a) >= x/(x+a) - eta`;
* **no room to drift.** Each `s` is a permutation, so
  `sum_z (f(sz) - f(z)) = 0`; boundedness then makes both the positive and the
  negative variation `o(N)`, hence
  `sum_(edges of L_G) |f(z) - f(y)| = o(N)`;
* **expansion converts variation into concentration.** The finite coarea
  identity `int_0^1 |boundary_A {f > t}| dt = sum_(edges in A) |f(z)-f(y)|`,
  split at the median and fed to the expansion of `A`, gives
  `gamma_G sum_(z in A) |f(z) - 1/2| <= sum_(edges in A) |f(z)-f(y)|`, so
  `|f - 1/2| <= delta_n -> 0` off `o(N)` vertices, and therefore
  `rho_n^(-1) <= M(y)/M(z) <= rho_n` with `rho_n -> 1` for nonexceptional
  `z, y` in the same ambient component.

**Consequence.** A transported component `p_i(C)` and the `Gamma`-component
`D` it almost lies in have approximately the same size, so `p_i(C)` occupies
more than half of `D`.  Distinct transported components are disjoint, so they
cannot select the same target: the matching is injective.

## The principle, stated once

Average a **bounded monotone function of component size**, never the size
itself.  The chapter's own account records that an intermediate attempt binned
`log M` on a randomly shifted grid and replaced the classes by bounded
midranks, with `Var(midrank) = (1 - sum_j p_j^3)/12`; the median normalization
above is the deterministic form of the same idea, and it compares sizes
precisely where the transport endpoints meet inside one ambient expander.

## Independently checked here

`Criterion/LocalCriterion` and `Criterion/SelectionOutput` perform this
matching in Lean, kernel-checked, as part of
[[one-sided-compression-nonsofic-criterion]].  The normalization is not
line-for-line the same, but the statement being proved -- transported
components match their targets injectively, off a negligible set -- is.
