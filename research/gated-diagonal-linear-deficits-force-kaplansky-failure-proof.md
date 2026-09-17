---
rg: 2
id: gated-diagonal-linear-deficits-force-kaplansky-failure-proof
kind: route
title: Split the gap into pointer and gated-rank parts, then pin every recovering combination to the unique inverse
target: gated-diagonal-linear-deficits-force-kaplansky-failure
requires: [bernoulli-rokhlin-deficit-has-a-finitary-witness, infinite-rokhlin-supremum-forces-surjunctivity]
artifacts:
  - research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md
---

This is a direct proof in Sections 2-4 of the artifact.

- **Theorem 1.** The chain rule splits the gap.
  - The pointer outputs are independent of the value inputs, so the value outputs are conditionally
    independent of `p(1)` given `J_F`.
  - For linear maps on a uniform vector, `I(Pv; Lv) = dim(row P ∩ row L) log q`.
- **Lemma 2 and Theorem 3.**
  - Diagonal gating makes the recovered space a direct sum over coordinates.
  - Coordinate `i` is recovered iff a combination `a` of active translates satisfies `a T_i = 1`.
  - Direct finiteness makes `a = T_i^{-1}` unique. Any `g_0 ∈ supp T_i^{-1}` must then be the
    translate of an active codeword.
  - A union bound over pointer values and stationarity give `P(d_i = 1) <= P(i ∈ I_{J_1})`.
- **Corollary 4.** Take the contrapositive inside the proof: the only failure is a one-sided unit.
- **Proposition 5.** The constants argument with characters of finite abelian groups.
- **Corollary 6.** It combines the above with the prerequisites:
  - the configuration semantics of `Phi` (`bernoulli-rokhlin-deficit-has-a-finitary-witness`);
  - Seward's Corollary 4.1 (`infinite-rokhlin-supremum-forces-surjunctivity`), through its
    contrapositive: `F_q[G]` not directly finite gives `h^Rok_sup < infinity`, hence `rho_{q'} = 0`.

The host list, linear sofic groups and Higman's group, is a consequence that uses the established
nodes `linear-sofic-group-algebra-is-stably-finite` and `higman-group-algebras-embed-in-division-rings`.
The main statement does not need them.
