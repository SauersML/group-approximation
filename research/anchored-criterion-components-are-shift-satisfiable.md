---
rg: 2
id: anchored-criterion-components-are-shift-satisfiable
kind: claim
title: Every anchored-amplifier requirement except the YES margin holds for the shifted standard reduction
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
distinct_from:
  positive-shift-trivializes-exact-combinatorial-soundness: that is the general instance transformation; this applies it to the standard QMA-complete reduction, checks it against each construction requirement of the anchored-amplifier region, and adds the converse from the root claim.
  amplifier-has-compatible-local-syndrome-effects: that is the open compatible construction demanded of the amplifier; this shows its construction clauses hold for a reduction whose YES margin is inverse polynomial, so they constrain nothing without that margin.
---

**ESTABLISHED (ordinary proof).** Let `R` be the standard reduction of
`kitaev-local-hamiltonian-is-qma-complete`, with normalized thresholds `a<b`
and `b-a>=1/p(n)`. Let `R_epsilon` apply the shift (PS0) of
`positive-shift-trivializes-exact-combinatorial-soundness` with a fixed rational
`epsilon` in `(0,1)`.

**Forward.** `R_epsilon` is a polynomial-time reduction from a QMA verifier to
constant-locality qubit Hamiltonians. On its NO outputs:

- (LPC1) holds with `beta=1`;
- the cost clause of `amplified-hamiltonian-has-a-constant-cost-rounder` holds
  with `C=1/epsilon`;
- the trivial syndrome data (PS5) satisfy clauses 1-3 of
  `amplifier-has-compatible-local-syndrome-effects`, (LSP1) of
  `local-syndrome-port-domination-at-each-gadget` with `C_0=1/epsilon` and
  `R=1`, and (EXA1) of `syndrome-conditioned-exactifier-exists`;
- `T_[m]=I` with `delta=epsilon` satisfies
  `amplifier-admits-a-uniform-local-kernel-resolution`;
- at every layer, `b_t=N_t<=(1/epsilon)e_t`, which gives (ANC1) with `r=1`
  and (BSA1) with `L=1/epsilon`.

Its YES outputs have `lambda_min=(1-epsilon)a+epsilon`. That is at least the
port-based floor `beta/C=epsilon`, and it falls below the optimal floor
`(1-epsilon)b+epsilon` only by `(1-epsilon)(b-a)<=1/p(n)`. So (YES1) of
`amplifier-preserves-yes-energy-below-the-floor` fails at any constant margin.

**Converse.** If `R*` witnesses `quantum-pcp-constant-gap-local-hamiltonian`
with `b*-a*>=gamma>0`, then `R*_epsilon` satisfies (LPC1) with `beta=1`, the
rounder criterion with uniform `C=1/((1-epsilon)b*+epsilon)`, and (YES1) with
margin `(1-epsilon)(b*-a*)>=(1-epsilon)gamma`, all for one reduction.

**Reading.** At a common reduction, the anchored criterion is equivalent to the
root claim. Every construction requirement other than the YES margin is met by
a reduction whose margin is inverse polynomial. Progress through
`qpcp-from-anchored-amplifier` must come from the margin, jointly with the
other requirements, or from a requirement the shift does not meet, such as
frustration-free YES outputs. On such outputs, a QMA-hardness reduction with
exactly implementable term measurements would also place QMA inside QMA_1,
and Aaronson's quantum oracle separation (arXiv:0806.0450) shows that cannot
be proved by a quantumly relativizing argument; see Section 6 of the artifact.
The proved obstructions of the region stand unchanged.
