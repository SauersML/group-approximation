---
rg: 2
id: global-walk-reducer-has-net-energy-gain
kind: claim
title: A constant-locality reducer loses less than the global tensor-walk gain
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/qpcp-integration-ledger-2026-09-20.md
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
distinct_from:
  amplifier-preserves-yes-energy-below-the-floor: that asks for the complete anchored-amplifier YES margin; this asks for a locality-reduction operation on every input from a precisely specified global tensor-walk image, with a numerical loss threshold and closure under iteration.
---

There exist a constant `k_0>=5`, a fixed integer `t>=2`, constants
`L,A,S>=1`, and a deterministic polynomial-time map `R_t` with
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
L < (t+1)/2.
```

The constant `S` absorbs all fixed walk and uniform-duplication factors.
If `B` is the maximum input term-description length in bits, including
support labels, every output term-description length is at most
`S(B+n+m+1)`. This linear bound is part of the requirement and controls
bit complexity under iteration.
Uniform duplication of the input clauses is allowed to realize the
fixed expander family and changes no Hamiltonian. The map receives the
explicit clause/tensor-factor description, not a ground state.

This is open. A family of reducers with loss `L_t=o(t)` for integer `t`
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
- A reducer whose outputs are sums of Pauli projectors, or of terms `I-Pi` with
  `Pi` a stabilizer code-space projector, is excluded unless QMA is in NP. Through
  `qpcp-from-global-walk-reduction`, the iterates would be a QMA-hard family of
  such terms with negligible YES energy and NO energy at least `g=1/[1+L/(1-L/B_t)]`, where `B_t=(t+1)/2`.
  `pauli-projector-hamiltonians-are-stabilizer-approximable` puts that promise
  problem in NP.

- The September 20 parity refinement of
  [[factorwise-complete-composition-returns-the-input-energy]] excludes
  universal independent-bit encodings with clause-private proofs and
  factorwise completeness error `eta_m=o(1/m)`: at every fixed
  `k_0>=2` and `t>=2` it forces `L>=(t+1)/2`. Shared proofs,
  correlated encodings and global completeness remain outside its scope.
- A restricted-domain alternative must start with a QMA-hard seed family
  and prove an invariant preserved by both operations, with the same
  all-state soundness, completeness and linear resource bounds. Such a
  construction would suffice without satisfying this universal claim;
  none is supplied by the present audit.

## Shared and coherent continuation

The [full-target continuation](artifacts/qpcp-full-target-continuation-2026-09-20.md)
examines escapes from the private-proof obstruction rather than assuming
that obstruction covers them. Its proved limitations are:

- [[shared-records-obey-complementary-check-uncertainty]]: a classical
  shared record pays a fixed complementary-check floor; noncommuting
  quantum records can evade it.
- [[coherent-records-have-exact-phase-energy]] and
  [[distance-code-local-tests-are-label-diagonal]]: coherent records have
  an exact data-only phase cost, and tests below classical code distance
  cannot connect logical labels even with shared quantum auxiliaries.
- [[distance-code-leakage-bounds-phase-energy]]: code leakage `delta`
  changes positive-contraction energy by at most `sqrt(delta)` after
  projection and label dephasing.
- [[diagonal-penalty-transitions-have-distance-order]]: with a diagonal
  penalty and `Delta-|z|>||V||`, transitions across distance `d` first
  appear at order at least `ceil(d/k)` and obey the stated geometric bound.
- [[one-copy-choi-tests-cannot-enforce-channel-legality]]: one static
  register cannot uniformly test legality while accepting every unitary
  channel, even with a nonlocal test and fixed auxiliary state.

No result above proves a universal impossibility of this reducer or
supplies it. Restricted-domain reductions, different encodings and
channel-dependent auxiliary proofs require their own complete analysis.
