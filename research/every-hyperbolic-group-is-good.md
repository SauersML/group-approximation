---
rg: 2
id: every-hyperbolic-group-is-good
kind: claim
title: Every word-hyperbolic group is good in Serre's sense
distinct_from:
  hyperbolic-finite-residual-is-torsion-free: that is the universal torsion-free-residual assertion, equivalent to universal residual finiteness; this is a profinite-cohomological assertion that implies it, with no converse known
  good-groups-have-no-persistent-finite-cohomology: that is a proved consequence of goodness for one group; this is the open assertion that every hyperbolic group is good
---

For every word-hyperbolic group `G`, every finite `G`-module `A` and every `q >= 0`, the
inflation map `H^q(G_hat;A) -> H^q(G;A)` is an isomorphism.

**Status: open.** By `good-cocompact-proper-groups-are-virtually-torsion-free` (H), this
implies that every hyperbolic group is virtually torsion-free and residually finite.
So it is at least as hard as Gromov's question. We did not check whether it is posed
as a named problem in the literature.

## Attempts

- **Through special cube complexes.** Hyperbolic virtually special groups are good
  (Kropholler–Wilkes, Theorem 9, recorded on
  `good-groups-have-no-persistent-finite-cohomology`). This covers exactly the
  cubulated hyperbolic groups, which are already residually finite. It dies at
  hyperbolic Kazhdan groups, which admit no proper cocompact cubulation, for example
  the density random groups above `1/3` (`gromov-density-random-groups-kazhdan-above-third`).
  No goodness theorem is known for them.
- **Only a weak form is needed downstream.** The route into
  `hyperbolic-finite-residual-is-torsion-free` uses only (G'). That is surjectivity of
  inflation with trivial `F_p` coefficients in large degrees, or even just onto the
  Chern–Quillen classes. The full isomorphism is never used.
- **The negative direction gives nothing by itself.** A residually finite hyperbolic
  group that is not good does not contradict residual finiteness. Non-goodness of a
  hyperbolic group decides neither root. What a counterexample to Gromov's question
  must fail is the specific surjectivity onto Chern–Quillen classes.
