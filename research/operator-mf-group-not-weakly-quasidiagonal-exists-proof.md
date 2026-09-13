---
rg: 2
id: operator-mf-group-not-weakly-quasidiagonal-exists-proof
kind: route
title: A quotientless LEF Kazhdan group is MF, and Ozawa--Thom forbids it from being weakly quasidiagonal
target: operator-mf-group-not-weakly-quasidiagonal-exists
requires: [lef-kazhdan-group-without-finite-quotients-exists, weak-qd-kazhdan-quotientless-group-is-trivial]
---

By `lef-kazhdan-group-without-finite-quotients-exists`, `G = EL_3(LC(X,F_q) ⋊ Z)` is:

- infinite;
- LEF, hence operator MF;
- Kazhdan;
- without nontrivial finite quotients.

If `G` were weakly quasidiagonal, `weak-qd-kazhdan-quotientless-group-is-trivial` would force
`G = 1`, contradicting infinitude. So `G` is operator MF and not weakly quasidiagonal.
