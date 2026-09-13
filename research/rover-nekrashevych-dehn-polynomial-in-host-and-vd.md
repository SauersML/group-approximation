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
