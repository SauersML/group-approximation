---
rg: 2
id: fpbs-finite-window-twisted-levels-disconnected-proof
kind: route
title: Extract witnesses with disjoint windows, pay delta once per extracted witness in the isolated-component path count, and localize small generating sets by finite-range patching
target: fpbs-finite-window-twisted-levels-disconnected
requires:
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
  - osin-isolated-components-bounded-by-relative-area
  - fpbs-twisted-level-graph-generates-cyclic-extension
artifacts:
  - research/artifacts/fpbs/docs/cross-line-transport-sets-finite-windows.md
  - research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md
---

Written derivation. Details are in the first artifact, Sections 2 and 3.

1. **Deterministic steps, unchanged.** Steps 1, 3 and 4 of `research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md`, Section 4, use no probability:
   - each edge has at most `2|S|` witness pairs;
   - the self-avoiding path count `P_l(s) <= |S|^l 2^((K+2)(l+1))`, from isolated `<t>`-components, (I1) and (I2) of that artifact, which are the two imported claims above.

2. **Disjoint windows.**
   - The pair `(u, m)` is the point `g = t^m u`, and `omega(g) = 1_A(g.x)` depends only on `x|_(W g)`.
   - `W g` meets `W g'` iff `g' in W^-1 W g`, which allows at most `D` points `g'`.
   - Greedy extraction gives, inside any finite `V`, at least `|V| / D` points with pairwise disjoint windows. Their events are independent under `mu`, so `P(omega = 1 on V) <= delta^(|V| / D)`.

3. **One path.**
   - A self-avoiding open path of length `l` has at most `(2|S|)^l` witness choice functions, each with at least `l/2` distinct values.
   - So `P(gamma open) <= (2|S|)^l delta^(l/(2D))`.
   - Main's sum with `delta^(1/D)` in place of `delta` gives `P(e <-> s) < 1` whenever `delta^(1/D) < delta_0`.

4. **Almost sure disconnection.**
   - The set of `x` whose graphing class is the whole orbit is `Gamma`-invariant, so ergodicity gives it measure 0 or 1.
   - By item (1) of `fpbs-twisted-level-graph-generates-cyclic-extension` and freeness, it is the event that the twisted return graph is connected. That event has probability at most `P(e <-> s) < 1`.

5. **Reduction.**
   - *Patching:* for any Borel `A`, the set `A ∪ ∪_s E_s^r(A)` has a generating transport graphing, because `S ∪ {t}` generates `Gamma`. This gives (c) ⇒ (a).
   - *Limits:* a generating `A` has `E_s^r(A)` decreasing to a null set, which gives (a) ⇒ (c).
   - *Localizing:* membership in `E_s^r(A)` is a Boolean function of `1_A` on `B_r x`. Replacing `A` by a `W_1`-local `A_1` with `mu(A Δ A_1) < eta` changes each `mu(E_s^r)` by at most `|B_r| eta`, and `E_s^r(A_1)` is `W_1 B_r`-local. Patching `A_1` gives (c) ⇒ (b).

6. **Window size.** Item 3 is the contrapositive of item 1.

This route is bookkeeping for a written deduction, not a formal verification.
