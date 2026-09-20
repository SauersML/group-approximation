---
rg: 2
id: steurer-hellinger-relaxation-rounding
kind: claim
title: The Hellinger relaxation sdp+ of a unique game (nonnegative functions on a probability space, disjoint supports per vertex) satisfies sdp+(G) >= 1 - C_3 eps ln k whenever sdp(G) >= 1 - eps, and sdp+(G) >= 1 - eps implies opt(G) >= 1 - 2 sqrt(2 eps) with no alphabet dependence (Steurer APPROX 2010 Theorem 3; Barak et al. FOCS 2008 as Steurer's Theorem 8)
distinct_from:
  steurer-parallel-repeated-unique-games-rounding: that imports the composed statement for G^l only (Theorems 1 and 7); this imports the two intermediate statements about sdp+ and its definition, which the composed statement is proved from, so that the tensor step can be redone for games other than G^l.
  cmm-unique-games-sqrt-log-k-rounding: that rounds the basic SDP with the log of the game's own alphabet; Theorem 8 here rounds sdp+ with no alphabet factor at all, and the log k is paid once, at the base, by Theorem 3.
---

**ESTABLISHED, BY CITATION.** Source: D. Steurer, *Improved Rounding for
Parallel Repeated Unique Games*, APPROX-RANDOM 2010 (LNCS 6302), Section 1.1,
Section 2.2 (eq. (2.6)–(2.8), Theorem 8) and Section 3. Theorem 8 there is
credited to B. Barak, M. Hardt, I. Haviv, A. Rao, O. Regev and D. Steurer,
*Rounding Parallel Repetitions of Unique Games*, FOCS 2008 ([2] of Steurer).
Credit is the authors'. Nothing is reproved here. The verbatim text is in the
route.

## Form used in this graph

- **Games.** A unique game `G` has vertex set `V`, alphabet `Σ` with
  `|Σ| = k >= 2`, and a probability distribution on constraints `(u, v, π)`,
  where `π` is a permutation of `Σ`. `opt` is its value. `sdp` is the basic SDP
  of `steurer-parallel-repeated-unique-games-rounding`.
- **(H0), the Hellinger value.** `sdp+(G)` is the supremum, over all
  probability spaces `(Ω, µ)` and all collections `{f_(u,i)}` of nonnegative
  functions in `L^2(Ω, µ)` with
  - `Σ_i ‖f_(u,i)‖^2 = 1` at every vertex `u`, and
  - `supp f_(u,i) ∩ supp f_(u,j) = ∅` for `i ≠ j` at every vertex `u`,

  of the objective `E_((u,v,π)~G) Σ_i ⟨f_(u,i), f_(v,π(i))⟩`.
- **(H1), Theorem 3.** There is an absolute constant `C_3 >= 1` such that for
  every unique game `G` with alphabet size `k >= 2`,
  `sdp(G) >= 1 − ε` implies `sdp+(G) >= 1 − C_3 ε ln k`.
- **(H2), Theorem 8.** For every unique game `G` and every `ε >= 0`,
  `sdp+(G) >= 1 − ε` implies `opt(G) >= 1 − 2 sqrt(2ε)`.

(H2) has no alphabet factor. That is the point of the relaxation: all
dependence on `k` enters through (H1), once, at whichever game (H1) is applied
to.

DERIVATION steurer-hellinger-relaxation-rounding-citation
