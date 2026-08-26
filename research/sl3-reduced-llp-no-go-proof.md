---
rg: 2
id: sl3-reduced-llp-no-go-proof
kind: route
title: Apply the regular-representation LLP obstruction to the residually finite lattice
target: sl3-reduced-group-cstar-has-no-llp
requires:
  - llp-regular-dominating-completion-forces-nonhyperlinear
---

Take `G=SL_3(Z)` and `pi=lambda_G`.  The group is finitely generated linear,
so Malcev residual finiteness makes it hyperlinear.  Its property `(T)` and
infinitude make it nonamenable.  Hence `pi` is a nonamenable representation,
and `lambda_G` is weakly contained in `pi` trivially.

If `C^*_pi(G)=C^*_r(G)` had LLP, the prerequisite would imply that `G` is
nonhyperlinear.  This contradicts residual finiteness.  Therefore the reduced
group C-star algebra has no LLP.
