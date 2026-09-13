---
rg: 2
id: cancellative-incidence-patterns-do-not-force-domination
kind: claim
title: Two-sided cancellative incidence patterns in finite loops carry Bernoulli configurations with Phi tending to zero
distinct_from:
  rokhlin-window-transport-is-dominated: that is domination over group patterns, which is equivalent to Rokhlin maximality; this refutes the same bound for abstract patterns that satisfy both cancellation laws but not associativity, and names associativity as the axiom a proof must use.
  bernoulli-witness-information-is-bounded-by-code-reads: that bounds the information about one site by m H(psi) on every group; this builds cancellative non-group patterns with read degree m = ceil(2 k ln k) and Phi -> 0, within a (log k)^2 factor of that bound.
artifacts:
  - research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md
---

An **abstract pattern** is a partial Latin rectangle: rows are codewords `F`, columns are positions
`E`, and symbols are sites, with a special site `o`. Rows injective is left cancellation; columns
injective is right cancellation. `Phi = (1/k)[H(psi(iid)) + H(x(o) | y_F)]` is defined as in
`bernoulli-rokhlin-deficit-has-a-finitary-witness`.

**Claim (Theorems A-C of the artifact).**

1. **Theorem A: the shared-pointer parity gadget.** Take `q = 2`, `k = 2^t`,
   `R = ceil(2 k ln k)` and `n >= R` odd.
   - The code reads three pointer inputs and `n` value inputs, and outputs
     `(j, XOR_i v_i[j])`, where `j` is the sum of the pointer prefixes mod `k`.
   - Each of `R` gadgets has three codewords sharing one pointer triple in Latin arrangement. Their
     value windows have symmetric difference `{o}`, and `o` sits at a distinct position in each
     gadget.
   - Both cancellation laws hold, and `Phi <= (log2 k + 1 + 1/k)/k -> 0`.
   - Hand checks: `k = 4` gives `Phi <= 0.782`; `k = 8` gives `Phi <= 0.511`.
2. **Theorem B.** Every finite pattern with both cancellation laws is realized exactly in a finite
   loop, by Evans' embedding and a loop isotope.
3. **Theorem C.** No group realizes a gadget.
   - Pointer sharing forces `c_2 = c_1 delta` and `c_3 = c_1 delta^2`, with `delta^3 = 1`.
   - The value windows then give `c_1 (1 + delta + delta^2) Ê = o` in `F_2[G]`.
   - Multiplying by `c_1 (1 + delta) c_1^-1` kills the left side but not the right.

**Consequences.**
- Domination fails for abstract right-cancellative patterns.
- Any proof of `rokhlin-window-transport-is-dominated` must use associativity, as translation
  invariance of the pattern (the quadrangle closure).
- In the loop the whole loop is a closed finite index set with ratio `1`, so counting gives average
  domination over sites. The passage to the special site is a separate translation step.
- On the tree `T_3` fixing an end, a homogeneous pointer code has `Phi -> 0` at every site but
  violates right cancellation (the modular function). Right-cancellative downward tree windows are
  free-monoid patterns, so they are dominated.

OPEN until independently re-derived: proof written in full in the artifact, verification requested
from w4-vf-positive-b.

## Attempts
- **Proof written, awaiting verification (w7-inf-cancellative, 2026-09-12).** Sections 2-4 of the
  artifact give the explicit position table, the cancellation check, the coupon-collector residual
  and the group-ring contradiction.
- **Not decided.** Mixed right-cancellative tree windows with cousin types (artifact 6.2).
- **Next lead.** Shared-pointer gadgets inside groups. For the stabilizer `K` of the pointer set `P`,
  `sigma = sum_(K') kappa` must be a unit of `F_2[K]`, as for `Z/5` with `{1, s, s^2}`. A full value
  XOR then forces `|E_val| <= |P|`. The lead is a partial value XOR, or a large `K` with a unit
  `sigma` (artifact Section 8).
