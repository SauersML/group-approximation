---
rg: 2
id: global-walk-reducer-has-net-energy-gain
kind: claim
title: A constant-locality reducer loses less than the global tensor-walk gain
artifacts:
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
distinct_from:
  amplifier-preserves-yes-energy-below-the-floor: that asks for the complete anchored-amplifier YES margin; this asks for a locality-reduction operation on every input from a precisely specified global tensor-walk image, with a numerical loss threshold and closure under iteration.
---

There exist a constant `k_0>=5`, a fixed even integer `t>=2`, constants
`L>=1` and `A,S>0`, and a deterministic polynomial-time map `R_t` with
the following properties. For every normalized `k_0`-local qubit
Hamiltonian `H=(1/m)sum_v h_v`, `0<=h_v<=I`, on `n` qubits with
polynomial-bit descriptions, use the global walk `G_t(H)` from
`global-walk-linearly-amplifies-hamiltonian-energy` with a fixed explicit
two-sided expander family of spectral bound at most `1/2`.

The output `H'=R_t(G_t(H))` is a normalized `k_0`-local qubit Hamiltonian
with positive-contraction terms and polynomial-bit descriptions, on
between `n` and `Sn` qubits with at most `Sm` terms, and

```text
lambda_min(H') >= lambda_min(G_t(H))/L,
lambda_min(H') <= A lambda_min(G_t(H))+2^(-n),
L < (3t+2)/16.
```

The constant `S` absorbs all fixed walk and uniform-duplication factors.
If `B` is the maximum input term-description length in bits, including
support labels, every output term-description length is at most
`S(B+n+m)`. This linear bound is part of the requirement and controls
bit complexity under iteration.
Uniform duplication of the input clauses is allowed to realize the
fixed expander family and changes no Hamiltonian. The map receives the
explicit clause/tensor-factor description, not a ground state.

This is open. A family of reducers with loss `L_t=o(t)` for even `t`
would suffice by choosing one large fixed value of `t`; loss bounded
independently of `t` is unnecessary.

## Attempts

- The proved global walk supplies the amplification and reduces the needed
  loss threshold to a linear function of `t`; it still multiplies locality
  by `t`, and so does not supply this reducer.
- Averaging the individual factors of every walk clause has exactly the
  original ground energy, by stationarity and the tensor-sum minimum.
  Therefore this particular operation does not produce net gain on any
  instance. A different composition construction is required.
- A one-call polynomial bound on output bit length is insufficient for
  the intended iteration. The explicit linear bound above closes that
  representation issue but supplies no mathematical locality reduction.
- [[local-or-simulation-has-linear-normalized-loss]] excludes a family
  of faithful clausewise simulators with fixed local encoding depth and
  loss `L_t=o(t)`: on a tensor-OR clause their loss is at least
  `t/(k_0 b^D)` with exact vacuum preservation. Fixed ancillas and
  noncommuting output terms do not avoid this bound. The requested
  instance-level map only controls ground energy, so it is not refuted;
  a successful construction may use that weaker obligation.
