---
rg: 2
id: perfect-correlated-mask-fourier-no-go-proof
kind: route
title: Solve the mask completeness linear program and evaluate its forced Fourier coefficients
target: perfect-correlated-masks-have-undamped-conditioned-spectrum
requires: []
artifacts:
  - research/artifacts/perfect-correlated-mask-fourier-no-go-2026-08-21.md
---

For an honest dictator `phi`, the long-code parity equation wins exactly when
`mu(phi)=1`.  Its loss is the nonnegative linear functional
`sum_mu p_mu(1-mu(phi))/2`.  Requiring zero loss for every active `phi`
therefore deletes every mask which is negative at any active point.  On the
remaining support, every character `chi_beta(mu)=prod_(phi in beta)mu(phi)`
with `beta` contained in the honest spectrum is identically one, proving the
Fourier assertion for arbitrary correlations.

Taking `beta=S` in the decoder domination inequality gives
`c^2<=1/|S|`.  The standard supported-answer random strategy wins the repeated
source with probability at least `1/|S|`, so this coefficient cannot make the
decoded lower bound strictly exceed the source soundness ceiling.

