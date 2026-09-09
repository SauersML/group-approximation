---
rg: 2
id: five-exterior-pencils-exclude-deletion-left-coefficients
kind: route
title: Reduce all left chart coefficients to five pencils and give an exact kernel for each
target: deletion-pair-has-no-left-chart-coefficient-split
requires: []
artifacts:
  - research/artifacts/kaplansky-lower-block-and-left-chart-exterior-formulas-2026-09-08.md
---

Parametrize the full exterior source by two tensor sectors (X,Y).
Let Phi_g be the original complete source map and Psi_a the map
after the constant lower transvection. For m=[[p,q],[r,s]] in K,
put alpha=r^2 and beta=ps+rq+rs. Its two target coordinates are

    beta Phi_g,+ + alpha Psi_a,+,
    beta^sigma Phi_g,- + alpha^sigma Psi_a,-.

The same form holds for a sum of elements of K. If alpha and beta
both vanish, the map is zero. Otherwise rescaling the targets
reduces it to v=alpha/beta in P^1(F_4). The second coordinate
uses the conjugate parameter v^sigma; using v in both coordinates
would give the wrong test for v=omega or omega^2.

The artifact gives literal finite tensor kernels for all five
parameters: periodic tails for zero and one, diagonal tensors
for infinity, and constant-tail prefix identities for omega and
omega^2. Each certificate is checked by expanding creation and
deletion operators. A nonzero scalar-extended source already
contradicts a split identity over F_2. Conditional expectation
onto the generated subgroup permits an arbitrary ambient L.

The argument needs a kernel for each pencil separately; it does
not assert that the five maps have a common nonzero kernel.
