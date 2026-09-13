---
rg: 2
id: rover-nekrashevych-dehn-polynomial-in-host-and-vd
kind: claim
title: A Röver–Nekrashevych group over a polynomial-Dehn host has polynomial Dehn function when V_d does
distinct_from:
  thompson-v-dehn-function-is-at-most-sextic: that bounds the Dehn function of V alone; this asks for an upper bound on the Dehn function of V_d(G) in terms of those of V_d and G.
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

**OPEN.** Let `G <= Aut(T_d)` be a finitely presented, finitely generated,
persistent, weakly diagonal, rational self-similar group, as in Zaremsky
arXiv:2305.15176, Corollary at TeX l.258. If `δ_(V_d)` and `δ_G` are
polynomially bounded, then `δ_(V_d(G))` is polynomially bounded.

**Source.** Zaremsky proves only the lower bound `δ_G ≼ δ_(V_d(G))` (TeX l.258)
and states the upper bound as a suspicion. TeX l.128, verbatim: "we suspect
that the Dehn function of any $V_d(G)$ should be bounded above by some
combination of the Dehn functions of $V_d(\{1\})$ and $G$, and this could
perhaps be approached by looking at the action of $V_d(G)$ on a simply
connected, cocompact truncation of the Stein--Farley complex of $V_d(G)$ (see,
e.g., \cite{skipper21}). In any case, this is all beyond the scope of the
present paper."

**Use.** With `higman-thompson-vd-has-polynomial-dehn-function` at `d = 10`
and the established `bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host`,
this would give a finitely presented simple group with polynomial Dehn function
containing `BS(1,2)`; see `bs12-poly-dehn-simple-host-via-rn-upper-bound`.

## Attempts

- **No explicit presentation to count on (lane solve-bh-rn-dehn, 2026-09-13).** Finite presentation of `V_d(G)` comes from Brown's criterion on the Stein–Farley complex (Zaremsky arXiv:2305.15176, TeX l.227, citing Skipper–Witzel–Zaremsky Theorem 4.15). No explicit finite presentation of `V_10(Gamma_2)` was found, so a direct van Kampen count is not available.
- **Push-down route, reduced.** Running Zaremsky's l.128 suggestion needs the additive descending-link lemma recorded on `higman-thompson-vd-has-polynomial-dehn-function`, plus polynomial distortion of the stabilizer copies `ι_w(G)` over cones of depth `O(L)`. For rational `G` the pushed-down leaf words have total length `O(L)` per root letter, which suggests linear distortion, but this is not a proof. See `research/artifacts/solve-bh-rn-dehn-2026-09-13.md` §4.
- **Projection remark (lane solve-vd-dehn-filling, 2026-09-13).** The square-word projection for `V_d` (`vd-dehn-bounded-by-standard-square-word-area`) should run on the Skipper–Witzel–Zaremsky complex of `V_d(G)`, with `G`-labels on pieces. Square words then carry `G`-relators on leaves, with area controlled by `δ_G`. Still unproved: the distortion estimate (conjugate `ι_w(G)` to a standard cone at cost `O(|w|)`, then use Zaremsky's quasi-retraction, arXiv:2305.15176 l.258) and the labelled analogue of polynomial square-word area. Not attempted beyond this remark.
