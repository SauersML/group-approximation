---
rg: 2
id: atomic-kraus-frames-extract-identity-dominated-rounding
kind: route
title: Prevent Kraus mass escape with the identity atom and extract a finite central frame algebra
target: identity-dominated-near-idempotent-channels-round
requires: []
artifacts:
  - research/artifacts/identity-dominated-channel-rounding-2026-09-08.md
---

Diagonalize each normalized Kraus frame and order its eigenvalues.
The frame after the first `r` vectors has operator norm at most
`1/(r+1)`. Bessel's inequality and the two bistochastic marginal
identities give the same bound for products with a tail on either
side. The Haar root-mean-square idempotence defect equals the frame
Hilbert--Schmidt defect and controls its operator norm. Consequently
the atomic limiting frame equals
its product frame.

The trace of that identity forces the two limiting Kraus marginals
to be the same projection. Complete-positive domination of the
identity makes that projection one, preventing loss of Kraus trace
mass. The resulting trace-class stationary frame commutes with
left and right multiplication by its Kraus algebra. Its support
contains the identity and hence the entire standard Hilbert space
of that algebra. Compactness makes the algebra a countable product
of finite matrix blocks.

On a block of degree `b` and trace weight `t`, the frame is the
scalar `t/b^2`. The identity domination inequality then gives
`sum b^2 <= 1/lambda`, so only finitely many blocks exist. Lift
their matrix units, transport the exact quadratic Kraus identities,
and fill the small complementary corner. Finite heads and vanishing
Kraus trace tails give uniform mixed-norm convergence of the channels.
