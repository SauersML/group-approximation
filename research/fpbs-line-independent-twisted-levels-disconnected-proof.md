---
rg: 2
id: fpbs-line-independent-twisted-levels-disconnected-proof
kind: route
title: Reuse the isolated-component path count, pay delta once per distinct fibre line along a path, and get the 0-1 law from i.i.d. rows
target: fpbs-line-independent-twisted-levels-disconnected
requires:
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
  - osin-isolated-components-bounded-by-relative-area
  - fpbs-twisted-level-graph-generates-cyclic-extension
  - fpbs-twisted-level-percolation-disconnected-at-low-density
artifacts:
  - research/artifacts/fpbs/docs/twisted-levels-line-independent-disconnection.md
  - research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md
---

Written derivation. Details are in the first artifact, Sections 2 and 3.

1. **Deterministic steps, unchanged.** Steps 1 and 3 of `research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md`, Section 4, use no probability:
   - each edge has at most `2|S|` witness pairs, with first coordinate an endpoint;
   - the self-avoiding path count `P_l(s) <= |S|^l 2^((K+2)(l+1))`, from isolated `<t>`-components and (I1) and (I2) of that artifact. These are imported through `hyperbolic-group-relative-to-maximal-elementary-subgroup` and `osin-isolated-components-bounded-by-relative-area`.

   Step 4 there is probabilistic: it sums the per-path bound over paths and fixes `delta_0`. This route takes the path count and `delta_0` from `fpbs-twisted-level-percolation-disconnected-at-low-density`, and item 2 redoes Step 4 with the per-path bound under (LI).

2. **One path under (LI).**
   - A self-avoiding open path `(w_0, ..., w_l)` has a witness choice function `c`, with at most `(2|S|)^l` choices. Its values have at least `l/2` distinct first coordinates, since row `w_i` serves only edges `i` and `i+1`.
   - The chosen pairs in one row are all open with probability at most `delta`.
   - Rows are independent, so `P(all chosen pairs open) <= delta^(l/2)`.
   - This reproduces main's bound `(2|S|)^l delta^(l/2)`, and main's two-point sum gives `P(e <-> s) < 1` for `delta < delta_0`.

3. **0-1 law.** By (LI.1) and (LI.2) the rows are i.i.d. So the `N`-action permutes i.i.d. coordinates freely with infinite orbits, and it is mixing. The event "connected" is `N`-invariant, so it has probability 0.

4. **Co-induced actions.**
   - **Freeness:** `nu` is atomless, and `g != e` moves some coset `<t>u` unless `u g u^-1 in <t>` for all `u in N`. For `g = t^k` that forces `N ⊆ E(t) = <t>`, which is false.
   - **The field:** for `A = {f(e) in B}`, `omega(u, m) = 1_B(T^m f(u))`, which satisfies (LI) with `delta = nu(B)`.
   - **Non-generation:** item (1) of `fpbs-twisted-level-graph-generates-cyclic-extension`.

5. **Bernoulli shift.** `[0,1]^Gamma` is the co-induction of the Bernoulli shift of `Z` via `f(h) = (x(t^j h))_j`. The sets `{f(e) in B}` are exactly the Borel sets measurable in `x|_<t>`. For `A` read off one line `x|_(v<t>)`, row `u` reads `{t^k phi^-k(v) u : k in Z}`. These sets are disjoint for distinct `u`, so (LI) still holds.

This route is bookkeeping for a written deduction, not a formal verification.
