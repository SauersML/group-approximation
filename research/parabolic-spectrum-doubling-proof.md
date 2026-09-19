---
rg: 2
id: parabolic-spectrum-doubling-proof
kind: route
title: Fixed conjugacy by the diagonal element transports the empirical parabolic spectrum by the fourth-power map
target: parabolic-spectrum-is-doubling-invariant
requires: []
---

In `SL_2(Z[1/2])`, direct multiplication gives
`hUh^(-1)=U^4` for `h=diag(2,1/2)`.  In an exact finite-dimensional unitary
representation, unitary conjugacy preserves the spectral multiset, so the
fourth-power map permutes that finite multiset; every point is consequently
a root of unity of odd order.  In an asymptotic representation the fixed
word identity has normalized-HS error tending to zero.  Hoffman--Wielandt
matching for normal matrices couples the eigenvalues of `U` and `U^4` with
mean square displacement tending to zero, which implies the asserted
Wasserstein-one convergence and the Fourier-coefficient identities.
