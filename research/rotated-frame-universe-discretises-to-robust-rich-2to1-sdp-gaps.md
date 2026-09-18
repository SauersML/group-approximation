---
rg: 2
id: rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps
kind: claim
title: The rotated-frame universe rich 2-to-1 game U_n discretises, at every fixed n and every eta > 0, to a finite rich instance with basic SDP value at least 1 - eta and integral value at most val(U_n) + eta
distinct_from:
  walsh-frame-rich-2to1-games-have-value-near-one: that shows one finite family of perfect SDP solutions (Walsh frames) forces value near 1; this uses the Haar-rotated frame universe, whose SDP solution is not Walsh-framed, and transfers its measurable value to finite instances without deciding what that value is.
  sd-rich-and-unique-games-sos-gaps-interconvert: that moves SoS gaps between unique games and rich games at completeness 1 - eta with eta tied to the alphabet; this gives basic-SDP completeness 1 - eta for every eta > 0 at a fixed alphabet, and moves no gap from unique games.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that is about reductions and skeletons; this is a fixed-instance compactness statement and says nothing about hardness.
artifacts:
  - experiments/rich-2to1-rotated-frame-universe-2026-09-17/check_universe_identities.py
---

**ESTABLISHED.** Proof: route `rotated-frame-universe-discretisation-proof`.

**The game U_n.** Rows of `X in O(2n)` are an orthonormal frame
`x_1, ..., x_(2n)` of `R^(2n)`. An edge is sampled as follows. Take `X` from
Haar measure. Take a uniform ordered pairing `P = (P(1), ..., P(n))` of `[2n]`,
with `P(b) = {a, a'}`. The right vertex is the Stiefel frame `Y = (y_b)` with
`y_b = (x_a + x_a')/sqrt2`. The 2-to-1 constraint is `pi(a) = b` iff
`a in P(b)`. Left alphabet `[2n]`, right alphabet `[n]`.
`val(U_n)` is the supremum of `Pr[f(X) in P(g(Y))]` over Borel maps
`f : O(2n) -> [2n]` and `g : V_n(R^(2n)) -> [n]`.

Since `P` is independent of `X`, the pairing law at every left vertex is
uniform. So `U_n` is rich in the sense of BKM Conjecture 7. Given `Y` and `P`,
the neighbour is `X' = H_P diag(I_n, R) H_P^T X` with `R` Haar on `O(n)`, where
`H_P` is the orthogonal change of basis to pair sums and pair differences. Hence
`sum_a x_a` is conserved along every two-step walk. Also
`z(X,a) = x_a/sqrt(2n)`, `z(Y,b) = y_b/sqrt(n)` is a perfect solution of the
GKOPTW basic SDP (Figure 1, quoted in
`walsh-frame-rich-2to1-games-have-value-near-one`). The artifact checks these
identities numerically.

**Theorem.** For every `n >= 2` and `eta > 0` there is a finite weighted rich
2-to-1 instance `G` with alphabets `[2n], [n]`, such that:

- the basic SDP value of `G` is at least `1 - eta`, and
- `val(G) <= val(U_n) + eta`.

**Corollary (conditional gap).** Suppose `val(U_n) <= delta` for some `n`.
Then no test of the form "accept iff basic SDP >= 1 - eta_0" with `eta_0 > 0`
depending only on `n` separates `val = 1` from `val <= delta + eta` for
`Gap-Rich-2-to-1_n`. Such a test accepts some instance of value at most
`delta + eta`. So the only open input for robust basic-SDP gaps at perfect
completeness is
`rotated-frame-universe-rich-2to1-game-has-vanishing-value`.

**Contrast.** The gaps obtained from right merges of Khot--Vishnoi instances
have completeness `1 - eta(n)` with `eta(n)` about `log(1/delta)/log n`. At a
fixed alphabet they are defeated by a small enough threshold `eta_0`. The
Walsh-framed perfect-SDP family has value near 1. This theorem closes the
"finite rich discretisation" half of the survivor recorded in the Attempts of
`rich-2to1-perfect-completeness-conjecture`. The integral-value half stays open.

## Attempts

* **2026-09-18, e2-w2-audit-ugc2 (calibration): adversarial audit. Verdict:
  survives, status kept ESTABLISHED. The load-bearing import was checked against
  the primary source, not against the graph.**

  * **The import is exact, and it matters.** The proof's only outside input is
    the constraint set of the GKOPTW basic SDP, quoted in
    `walsh-frame-rich-2to1-games-have-value-near-one`. I pulled the paper
    (Guruswami, Khot, O'Donnell, Popat, Tulsiani, Wu, *SDP gaps for 2-to-1 and
    other Label-Cover variants*, ICALP 2010,
    `https://www.cs.cmu.edu/~odonnell/papers/2-to-1-gaps.pdf`) and extracted its
    text stream. Figure 1 reads, verbatim:

    > maximize `E_(e=(u,v) in E) [ sum_(i,j in psi_e) <z(u,i), z(v,j)> ]`
    > subject to `sum_(i in [R]) ||z(v,i)||^2 = 1` for all `v in V`,
    > `<z(v,i), z(v,j)> = 0` for all `i != j in [R]`, `v in V`.
    > Fig. 1. SDP for Label-Cover

    There is **no** nonnegativity constraint `<z(u,i), z(v,j)> >= 0` and no
    triangle or consistency constraint. This is exactly what Step 4 needs: the
    cell representatives are orthonormal frames, so both constraints hold
    exactly and the only loss is in the objective. Had Figure 1 carried the
    nonnegativity constraints that some Label-Cover relaxations do, the
    perturbed solution could violate them by `2 eps` at cross-cell pairs and
    Step 4 would break. The graph's quote is faithful.
  * **Arithmetic re-derived.** `y_b = (x_a + x_a')/sqrt2` gives
    `<x_a, y_(pi(a))> = 1/sqrt2`; dividing by `sqrt(2n) sqrt(n) = n sqrt2` gives
    `1/(2n)` per label and `1` over the `2n` labels, so the universe solution is
    perfect. `| <x', y'> - <x, y> | <= ||x - x'|| + ||y - y'|| <= 2 eps` for unit
    vectors, and `2n * 2 eps / (n sqrt2) = 2 sqrt2 eps`, as claimed. Norms sum
    to `2n/(2n) = 1` on the left and `n/n = 1` on the right.
  * **Value direction.** `val(G) <= val(U_n)` is correct: the cell maps are
    Borel, `W` is the pushforward of the edge law under `(cell, cell, id)`, and
    the acceptance predicate factors through `(cell(X), cell(Y), P)`.
  * **Richness.** BKM Definition 5, as recorded in `rich-2to1-games-conjecture`,
    asks that a uniformly sampled incident edge induce a uniformly random
    perfect pairing of the left alphabet. `P` is independent of `X`, so
    `Pr[P | X in C_c]` is uniform on ordered pairings and hence uniform on the
    `(2n-1)!!` matchings; Step 5 says explicitly that the rounding keeps
    `Pr[P | c]` exactly uniform. Checked.
  * **Parallel edges are harmless.** For `eps < 1/4` a cell pair `(c, d)`
    carries at most one `P`: pair sums of an orthonormal frame under two
    different pairings are at distance `1` (sharing a point) or `sqrt2`
    (disjoint), far above `3 eps`. The per-edge argument of Step 4 is valid in
    any case, since each `(c, d, P)` of positive weight has its own witness.
  * **Artifact re-run.** `check_universe_identities.py` runs in 0.14 s and
    prints `all identities hold; worst objective loss / eps = 0.011`, well
    inside the proved `2 sqrt2` slack. The claim asserts no numeric value, so
    there is nothing to mismatch.
  * **Scope note, no narrowing needed.** The theorem is unconditional and does
    not by itself exhibit a gap; the gap is the stated Corollary, conditional on
    `val(U_n)` being small. Note the quantifier: the Corollary assumes
    `val(U_n) <= delta` for *some* `n`, whereas the parent
    `rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps` needs
    `val(U_n) -> 0`, which is exactly what
    `rotated-frame-universe-rich-2to1-game-has-vanishing-value` states. The two
    line up. Also note that the instance has basic SDP value `1 - eta`, not `1`,
    so this is a *thresholded-test* statement, which is the form the parent asks
    for, not a literal perfect-SDP gap.
