---
rg: 2
id: fpbs-one-relator-twice-used-letter-fixed-price-proof
kind: route
title: Match each boundary cycle to the twice-used-letter edge toward its parent in a finite dual BFS forest
target: fpbs-one-relator-twice-used-letter-fixed-price
requires:
  - weinbaum-proper-subwords-of-relator-nontrivial
  - magnus-moldavanskii-hierarchy-with-decidable-edges
  - fpbs-bernoulli-morse-collapse-criterion
  - one-relator-group-cost-equals-first-l2-betti-plus-one
  - fpbs-bernoulli-maximal-cost
artifacts:
  - research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md
  - experiments/fpbs-dual-forest-morse-2026-09-17/check_two_incidences.py
---

Written proof. Sections 2-4 of the artifact give it in full.

1. **Normal form.** Rotate `w` and possibly invert `s` so that
   `w = s v_1 s^eps v_2`, with `v_1, v_2` words in `S \ {s}`.
   - If `eps = +1`, then `v_1 != v_2`, since `w` is not a proper power.
   - If `eps = -1`, then `v_1` and `v_2` are nonempty.
   - The Freiheitssatz makes `<s>` infinite cyclic, so `Gamma` is infinite.
2. **Embedded cycles.** By Weinbaum, applied to cyclic permutations of `w^m`,
   the closed path reading `w^m` visits `m|w|` distinct vertices. So it crosses
   each edge once, which is (M1), and `w` has order exactly `m`. Cycles are the
   cosets `gamma<w>`.
3. **Two incidences.** Every `s`-edge `{g, gs}` lies on exactly two cycles:
   `g<w>` and `g t<w>`, where `t = (s v_1)^{-1}` or `t = s v_1^{-1} s^{-1}`.
   They are distinct by step 2.
4. **Infinite dual components.** The dual graph `D` (cycles adjacent through
   `s`-edges) is loopless and `2m`-regular. The component of `<w>` is
   `<w, t><w>`. The group `<w, t>` contains `v_1^{-1} v_2` if `eps = +1`, and
   `t` itself, conjugate to `v_1^{-1}`, if `eps = -1`. In either case this is a
   nontrivial element of the free Magnus subgroup `<S \ {s}>`, hence of
   infinite order. So every component is infinite.
5. **Borel forest on the Bernoulli space.**
   - Choose one base point per cycle by the least first label; the
     representatives have density `1/m`.
   - Mark a representative when its independent second label is below `eps`.
     Almost surely every infinite component contains a marker.
   - Match each unmarked representative to the first `s`-edge that leads to a
     cycle one step closer to the markers.
   - Injectivity (M2) follows from the strict decrease of distance.
6. **Well-foundedness (M3).**
   - A child `e'` of `M(c)` must be `M(c')` with `P(c') = c`, because an
     `s`-edge has only two incidences. Chains of children are therefore
     descending paths in one tree.
   - Mass transport for the free p.m.p. shift (`sum over the orbit, integrate`)
     shows that roots with infinite trees form a null set. So trees are finite
     almost surely.
7. **Costs.**
   - Theorem A gives `C(b) <= |S| - (1 - eps)/m` for every `eps`.
   - Poulin-Wróbel and identity (I) give `z(Phi_S) = 1/m`, hence `m(R) = 0`.
   - `cost(Gamma) = |S| - 1/m` (Poulin-Wróbel) and Bernoulli maximality give
     `C(a) = |S| - 1/m` for every free p.m.p. action `a`.

Trust surface. Poulin-Wróbel is an unrefereed preprint, and Weinbaum's
statement was read from a secondary source. Everything else is proved in the
artifact or is an established node. There is no Lean counterpart.
