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
