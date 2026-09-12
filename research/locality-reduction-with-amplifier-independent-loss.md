---
rg: 2
id: locality-reduction-with-amplifier-independent-loss
kind: claim
title: Amplified layered Hamiltonians reduce to constant locality with a soundness loss independent of the amplification parameter
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
distinct_from:
  bmvz-iterable-tensor-gap-amplification: that is the proved locality-increasing amplification step; this is the missing composition step that must bring locality back to a constant while losing only a t-independent factor.
  quantum-pcp-constant-gap-local-hamiltonian: that is the hardness conjecture; this is an energy-affine reduction on amplified instances. With the amplifier it implies the conjecture, but the conjecture as a decision statement does not supply this map.
---

**OPEN.** The quantum analogue of Dinur's alphabet reduction. `L(k,g,omega)`
denotes normalized layered Hamiltonians (Definition 1.6 of arXiv:2510.01333)
of `k`-local qubit projections with rational polynomial-bit entries, at most
`g` layers, and `omega_min<=omega`.

There must be constants `k_0>=5`, `g_0>=36`, `omega_0>=70` and `c>0`, and for
every integer `t>=2` constants `S_t` and `A_t`, together with a deterministic
polynomial-time map with the following property. The amplified Hamiltonian
`H^(2t)` of every `H` in `L(k_0,g_0,omega_0)` on `N` qubits with `M` clauses
maps to some `H'` in `L(k_0,g_0,omega_0)` on at most `S_t N` qubits with at most
`S_t d^(2t) M` clauses, satisfying

```text
lambda_min(H') >= c * lambda_min(H^(2t)),                         (RED1)
lambda_min(H') <= A_t * lambda_min(H^(2t)) + 2^(-N).              (RED2)
```

**`c` must not depend on `t`.** The size factor `S_t` and completeness factor
`A_t` may depend on `t`, since `t` is a fixed constant during iteration.

By `qpcp-by-dinur-iteration`, this claim with
`bmvz-iterable-tensor-gap-amplification` gives
`quantum-pcp-constant-gap-local-hamiltonian`. The lower bounds `k_0>=5`,
`g_0>=36` and `omega_0>=70` make the class contain the QMA-complete starting
family of that source's Corollary 8.4.

**The classical analogue holds.** An assignment tester encodes the whole local
assignment of a large clause by a code of constant relative distance, so a
violated clause is far from every satisfying encoding and is detected with
constant probability. Its loss does not depend on the alphabet
(Dinur--Reingold). The quantum obstacles are no-cloning, which forbids the
duplicate-and-compare consistency tests, and local indistinguishability,
which hides logical information from every local term when a quantum code has
constant relative distance (Bafna--Vyas, ECCC TR26-150).

## Attempts

- **Unfold each amplified clause into the average of its factors.** Dead:
  `unfolding-tensor-clauses-returns-the-original-gap` proves that the unfolded
  Hamiltonian has exactly the input ground energy, so its loss is at most
  `sqrt(log t/t)/eta` and depends on `t`.
- **Perturbative gadgets** (Kempe--Kitaev--Regev; Oliveira--Terhal). These
  reduce locality, but the known constructions recover the gap only up to a
  factor depending on the gadget order and energy scales, which grow with the
  clause locality `2t k_0`. No lower bound for gadgets is proved here; no
  gadget with `t`-independent loss is known.
- **Clock-encode a coherent clause measurement.** BMVZ Lemma 7.6 measures a
  clause by an ancilla AND tree of depth `O(log m)`. Encoding that circuit with
  a clock construction pays the circuit-size-dependent promise-gap loss of
  clock Hamiltonians, which grows with `t`.
- **Change local dimension instead of locality.** Not applicable: the
  amplifier already works on qubits and grows locality, not dimension.
