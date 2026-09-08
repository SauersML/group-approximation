---
rg: 2
id: range-cover-deficit-certifies-no-finite-syndrome-cost
kind: claim
title: A state seeing total local range mass below one gives an explicit infinite-cost syndrome certificate
artifacts:
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
  - scripts/check_qpcp_chain_obstruction.py
  - research/artifacts/qpcp-fixed-term-chain-replay-2026-09-07.json
distinct_from:
  finite-syndrome-cost-is-a-kernel-support-cone-test: that gives a general separating alternative; this constructs a separator directly from a density matrix with deficient local range coverage, without solving a cone problem.
  nonorthogonal-pair-forbids-single-term-syndrome-ports: that treats two qubit projectors; this supplies a matrix certificate for arbitrary frustrated finite-dimensional instances and energy neighborhoods.
---

For a frustrated instance, let `P_a` project onto the range of the energy
neighborhood sum `A_a`. If a density matrix `rho` satisfies
`eta=1-sum_a Tr(P_a rho)>0`, no exactifying instrument obeys
`F_a<=C_0 A_a` for any finite `C_0`.

With `D=dim H`, the explicit matrices
`Y=rho-sum_a P_a rho P_a-eta I/(2D)` and
`X_a=(2+8D/eta)(I-P_a)` have positive `X_a`, zero energy denominator,
`Tr(Y)=eta/2>0`, and `sum_(a in S)X_a>=Y` for every feasible fault set.
The artifact proves these inequalities without an SDP solver.
