---
rg: 2
id: nonhyperlinear-from-regular-actor-second-fold-bias
kind: route
title: Contradict the canonical arcsine law with a positive second-fold bias
target: non-hyperlinear-group
requires:
  - regular-actor-balanced-swap-has-positive-second-fold-bias
  - canonical-arithmetic-swap-fold-gram-is-arcsine
  - arithmetic-double-swap-extension-is-binary-coset-wreath
---

Assume the arithmetic double, equivalently its binary swap extension `E`,
is hyperlinear.  Choose canonical normalized-Hilbert--Schmidt microstates of
`E` and round the swap to self-adjoint involutions `S_n`.  Their restrictions
to `A` converge to the regular character and `tr(S_n)->0`, so the
regular-actor bias claim gives

```text
liminf_n Re tr((rho_n(h)S_nrho_n(h)^*S_n)^2)>=epsilon_*>0.
```

But the established canonical arcsine law gives convergence of the same
quantity to zero.  This contradiction excludes canonical microstates of
`E`.  The index-two swap-extension equivalence then excludes hyperlinearity
of the explicit finitely presented arithmetic double.
