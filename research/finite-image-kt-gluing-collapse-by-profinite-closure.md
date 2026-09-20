---
rg: 2
id: finite-image-kt-gluing-collapse-by-profinite-closure
kind: route
title: A finite-index equality subgroup contains the profinite closure of Gamma
target: finite-image-kt-gluings-kill-laurent-differences
requires:
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
---

The prerequisite and its Step 4 proof identify the profinite closure of
Gamma inside G with N=EL_r(R). Given rho_0,rho_1 as in the target,
the equality set H={g:rho_0(g)=rho_1(g)} is a subgroup containing
Gamma. It contains ker(rho_0) intersect ker(rho_1), a finite-index
normal subgroup because both images are finite. Thus H is a closed
finite-index subgroup and contains N, proving equality on N.

The matrix e_12(x_1^(-1)) lies in the Laurent elementary group but
not in the polynomial subgroup, as seen from its matrix entry.
The normal form theorem for amalgamated free products makes the
two-letter word i_0(n)i_1(n)^(-1) nonidentity. The induced unitary
representation sends it to I by equality on N, so its trace is 1.
No approximation limit can turn that fixed value into 0.
