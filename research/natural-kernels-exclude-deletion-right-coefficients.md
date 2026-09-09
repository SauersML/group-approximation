---
rg: 2
id: natural-kernels-exclude-deletion-right-coefficients
kind: route
title: Normalize the right tensor flip and transfer natural kernels to the full exterior source
target: deletion-pair-has-no-right-chart-coefficient-split
requires: []
artifacts:
  - research/artifacts/kaplansky-right-chart-coefficient-natural-kernel-transfer-2026-09-08.md
---

Write D_z(X,Y)=(zX,z^sigma Y), and let tau flip both tensors.
For a right chart matrix [[p,q],[r,s]], its complete source map is

    Phi_g D_alpha + Phi_g D_beta tau + Psi_b D_gamma,
    alpha=p(r+s), beta=r(p+q), gamma=r(r+s).

For a sum of chart matrices, sum the three coefficients. If
delta=alpha+beta=0, every flip-symmetric source is killed. If
delta is nonzero, source rescaling and the involution
I+D_(beta/delta)(I+tau) reduce the map to

    Phi_g+Psi_b D_(gamma/delta).

The second term kills symmetric tensors, so the normalization
is exact. This is the complete map of diag(a+b m_v,b), with
v=gamma/delta and m_v multiplication by v on the binary field
coordinate. The first auxiliary block need not be invertible.

Any nonzero natural kernel of that first block gives a nonzero
exterior source kernel: the relative character images of the two
components agree, making their cross projections a diagonal
alternating expression. The artifact treats zero-component cases
separately. For v=1,omega,omega^2, natural kernels follow from
(t_0+t_1)(s_0+s_1)=0 and the constant zero and one tails. For
v=0, the previously established periodic-tail kernel applies.
