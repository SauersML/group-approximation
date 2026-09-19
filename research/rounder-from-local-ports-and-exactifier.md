---
rg: 2
id: rounder-from-local-ports-and-exactifier
kind: route
title: Bounded-overlap syndrome ports and a conditional exactifier assemble the rounder
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [local-syndrome-port-domination-at-each-gadget, syndrome-conditioned-exactifier-exists, bounded-overlap-syndrome-energy-accounting, commuting-syndrome-domination-gives-a-rounder]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

## Why sufficient

`local-syndrome-port-domination-at-each-gadget` supplies mutually commuting
projectors `B_j` on the syndrome register, an isometry `W`, neighbourhoods
`N(j)` with occurrence at most `R`, and the per-port inequality

```text
W^* B_j W <= C_0 sum_(a in N(j)) h'_a.                          (LSP1)
```

Evaluate (LSP1) in an arbitrary input state `rho` and set

```text
q_j = Tr(B_j W rho W^*),     e_a = Tr(h'_a rho).
```

Then `q_j <= C_0 sum_(a in N(j)) e_a`, which is the local charge hypothesis
of `bounded-overlap-syndrome-energy-accounting` with `L = C_0` and `D = R`.
That lemma returns

```text
sum_j q_j <= C_0 R sum_a e_a,
```

and, since the `B_j` commute, the left side is exactly `E|S|` for the joint
measurement outcome `S = {j : B_j reads 1}`.  This is clause (2) of the
rounder definition with `C = C_0 R = O(1)`.  Clause (1) is
`syndrome-conditioned-exactifier-exists`.  Assembling the two clauses into a
single instrument is `commuting-syndrome-domination-gives-a-rounder`.

## Where the incidence lemma comes from

Nothing new is counted here.  The local-to-global step is the graph's
existing `bounded-overlap-syndrome-energy-accounting`, used verbatim under
the dictionary above; that node was written for normalized Hilbert--Schmidt
relator energies, and the dictionary is the only thing this route adds to it.
Note also that (LSP1) quantified over all input states is *equivalent* to the
operator inequality, not weaker than it, so nothing is lost by evaluating
first.
