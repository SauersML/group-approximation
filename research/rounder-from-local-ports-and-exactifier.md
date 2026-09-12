---
rg: 2
id: rounder-from-local-ports-and-exactifier
kind: route
title: One compatible local syndrome construction supplies a constant-cost rounder
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [amplifier-has-compatible-local-syndrome-effects, local-syndrome-port-domination-at-each-gadget, syndrome-conditioned-exactifier-exists, local-syndrome-synthesis-has-an-exact-sdp-test, bounded-overlap-syndrome-energy-accounting, commuting-syndrome-domination-gives-a-rounder]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
---

## Why sufficient

Choose the **single tuple** supplied by
`amplifier-has-compatible-local-syndrome-effects` for each relevant NO
output of the same amplifier. Its isometry `W`, commuting projectors
`B_a`, and neighborhoods `N(a)` satisfy

```text
W^* B_a W <= C_0 sum_(b in N(a)) h'_b,
```

with uniform `C_0` and occurrence at most `R`. Each flag names a term that
may be left unsatisfied; a gadget-based proposal must first use its explicit
map to term faults and include the map's bounded multiplicity in the cost.

Let `Pi_S` be the joint projector of these same ports and put
`E_S=W^*Pi_S W`. The tuple also guarantees that `E_S=0` for every infeasible
fault set. These are the primal constraints of
`local-syndrome-synthesis-has-an-exact-sdp-test`. Apply its fixed-measurement
recovery argument to these effects: an unrestricted conditional CPTP recovery returns a
normalized state on the original Hamiltonian space, exact on every term
outside the measured `S`. No replacement of the physical `W` by a generic
dilation is made in this argument.

For any input state `rho`, define
`q_a=Tr(B_a W rho W^*)` and `e_b=Tr(h'_b rho)`. The displayed domination
gives `q_a <= C_0 sum_(b in N(a)) e_b`. The existing finite incidence lemma
`bounded-overlap-syndrome-energy-accounting`, with `L=C_0` and `D=R`, gives

```text
E|S| = sum_a q_a <= C_0 R sum_b e_b.
```

If a supplied constant is zero it may be increased to a positive constant
before applying that lemma. Joint commutativity identifies the sum of the
marginals with the expected cardinality of the actual measured set. Thus
the same instrument has both exactness and cost at most `C=C_0 R=O(1)`;
`commuting-syndrome-domination-gives-a-rounder` completes the implication.
An explicit gadget-to-term map with multiplicity `M=O(1)` changes the bound
to `C=M C_0 R` and must preserve the same exactness statement.

## Construction boundary

This route no longer accepts separate existential port and recovery
claims as though their witnesses automatically agreed. Both components
must be extracted from `amplifier-has-compatible-local-syndrome-effects`.
The component claims remain named prerequisites to retain their existing
construction interfaces and attack history. They are redundant projections
once the shared tuple is supplied, as the two extraction routes show;
proving them separately still cannot replace the common-tuple prerequisite.
The primal/dual criterion in
`local-syndrome-synthesis-has-an-exact-sdp-test` gives a finite audit of the
local inequalities and joint support, with exact separating certificates
for some failed candidates. It does not supply the open uniform
construction, its physical realization, or the QMA hardness reduction.
