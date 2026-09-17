---
rg: 2
id: titz-witzel-kernel-kazhdan-constant-and-no-finite-quotient
kind: claim
title: The Titz--Witzel group K used for long-scale monodromy is finitely presented, has no nontrivial finite quotient, and has a positive distance-form Kazhdan constant for a finite generating set
distinct_from:
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports Theorem A and Corollary B, where Gamma_i^q = pi_1(Y_i^q) are NOT residually finite and simplicity is stated only for their finite residuals Gamma^_i^q; this asks for exactly the three hypotheses of kazhdan-sofic-models-carry-long-scale-monodromy for a named group K, with a (KP) Kazhdan constant rather than bare property (T).
  kazhdan-sofic-models-carry-long-scale-monodromy: that is the general local-to-global monodromy bound; this is only the hypothesis check needed to apply it to the kernel in its consequence (C2).
  kazhdan-hyperbolic-group-without-finite-quotients: that asks for a hyperbolic example; this is about the Titz--Witzel kernel.
---

**OPEN.** Premise split off on 2026-09-17 when a referee refuted the route
`kazhdan-sofic-models-carry-long-scale-monodromy-proof` at its consequence (C2).

**Statement.** Let `K` be the group that (C2) of
`kazhdan-sofic-models-carry-long-scale-monodromy` calls `Gamma_1^2`, with a finite symmetric
generating set `S`. Then:

1. `K` is finitely presented;
2. `K` has no nontrivial finite quotient;
3. some `kappa > 0` is a Kazhdan constant for `S` in the convention (KP) of
   `kazhdan-consistent-partial-models-round-to-finite-actions`.

**Why it is not yet established.** In `titz-witzel-simple-kazhdan-cat0-lattices-exist` the groups
`Gamma_i^q = pi_1(Y_i^q)` are the lattices that are NOT residually finite, and simplicity is
claimed only for their finite residuals `Gamma^_i^q`. That node never says that `Gamma_1^2` itself
is simple or has no finite quotient. `K = Gamma_1^2` is simple only in the paper's other notation
(Gamma = the finite residual of barGamma, Theorem 4.1: no finite-index subgroups), which appears in
the artifact `research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md` and in
`radu-bmw-lattice-embeds-in-titz-witzel-kernel-citation`. Property (T) is only asserted there, and
nothing imported gives a positive Kazhdan constant in the distance form (KP).

**Likely closure.** Take `K` to be the finite residual `Gamma^_1^2`, cite its finite index in the
type-`F` group `Gamma_1^2` (finite presentation), Corollary B (simple and infinite, hence no
finite quotient), and the standard equivalence between property (T) and a positive Kazhdan
constant for a finite generating set, stated verbatim in the (KP) form.

## Attempts

None yet.
