---
rg: 2
id: wreath-lamp-corner-is-coset-percolation
kind: claim
title: Lamp corners of a generalized wreath product are group-ring operators restricted to random unions of cosets
distinct_from:
  kun-thom-wreath-galois-unequal-atomic-element: that is the open witness question; this is an exact model for the spectra of one family of candidates
---

**ESTABLISHED.** Let `W = (Z/2) wr_(G/Gamma) G`, let `e_Gamma` be the lamp at
the coset `Gamma`, put `p = (1 + e_Gamma)/2`, and let `X in Z[G]` be
self-adjoint. For every continuous `phi` with `phi(0) = 0`,

```text
tau_W( phi(p X p) ) = E_omega < phi(1_U X 1_U) delta_e , delta_e >_(l^2 G),
```

where `U` is a random union of right cosets `Gamma h`, each included
independently with probability `1/2`. The operator `X` acts by left
translation, `delta_h -> delta_(gh)`. The integral element is `P X P` with
`P = 1 + e_Gamma = 2p`.

Letters `g` in `Gamma` keep each right coset fixed; letters outside `Gamma`
jump between cosets. So if `X` is supported in `Gamma`, the spectral measure
is `(1/2) delta_0 + (1/2) mu_X`, whose atoms are those of an operator over the
sofic group `Gamma`. Galois-unequal atoms, if any exist, must come from
letters outside `Gamma` joining open cosets: correlated site percolation on
`Cay(G)` with coset-constant spins.
