---
rg: 2
id: joint-syndrome-support-characterizes-exactifiability
kind: claim
title: A fixed joint syndrome measurement admits unrestricted exact recovery exactly on feasible fault labels
artifacts:
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
distinct_from:
  syndrome-conditioned-exactifier-exists: that asks for recovery for the proposed amplified Hamiltonian's particular ports; this characterizes recovery for an arbitrary fixed finite-dimensional measurement and does not construct the ports.
  commuting-syndrome-domination-gives-a-rounder: that converts an assumed exactifier and an assumed energy inequality into a cost bound; this characterizes the exactifier assumption by the support of every joint outcome.
---

Let `h_1,...,h_m >= 0` act on a nonzero finite-dimensional space. A label
`S subset [m]` is feasible when `intersection_(a not in S) ker h_a` is
nonzero. For a fixed measurement instrument with input POVM effects `E_S`,
outcome-conditioned CPTP recovery exact outside `S` on the original space
exists for every input and every occurring outcome if and only if `E_S=0`
for every infeasible label. Recovery may discard its input and need not be
efficient or preserve logical information.

For commuting syndrome data this concerns the effects `W^* Pi_S W` of the
same isometry and joint projectors used in the cost estimate. Every joint
POVM can be dilated to commuting single-bit syndrome tests, but the
explicit square-root dilation supplies no physical-locality or circuit
bound. These are ordinary mathematical statements, not Lean certificates.
