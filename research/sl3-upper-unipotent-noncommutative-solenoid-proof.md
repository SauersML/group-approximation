---
rg: 2
id: sl3-upper-unipotent-noncommutative-solenoid-proof
kind: route
title: The root commutator and central disintegration give the corrected SL3 unipotent spectral model
target: sl3-upper-unipotent-is-a-noncommutative-solenoid-field
requires:
  - heisenberg-solenoid-trace-torsion-dichotomy
---

Matrix multiplication gives

```text
e_12(x)e_23(y)e_12(x)^(-1)e_23(y)^(-1)=e_13(xy).
```

Taking `x=y=1` proves that the upper-unipotent subgroup `N` is nonabelian.
SNAG applies to a commuting family, so it cannot give a joint PVM for the
three root subgroups.  Equivalently, the claimed identification
`C*(N)=C(hat(R)^3)` would make the displayed nontrivial commutator trivial.
This directly invalidates `sl3-carrier-rank-two-solenoid-action-proof`.

The center is `c(R)`, so its commuting image has a PVM on `S_p=hat(R)`.
Disintegrating a trace over that PVM and imposing central character `zeta`
turns the multiplication law

```text
a(x)b(y)c(z) a(x')b(y')c(z')
 =a(x+x')b(y+y')c(z+z'-x'y)
```

into the multiplier
`sigma_zeta((x,y),(x',y'))=zeta(-x'y)` on `R^2`.  This is precisely the
fiber construction proved in `heisenberg-solenoid-trace-torsion-dichotomy`.
Diagonal conjugation scales `x,y,z` by their root weights and therefore
maps the fiber at `zeta` to the correspondingly scaled central character;
it does not remove the multiplier.

For the canonical trace, restriction to `c(R)` is `delta_0`, whose Fourier
measure is Haar on `S_p`.  Haar has no atoms and hence gives zero mass to
the countable torsion subgroup.  The cited torsion dichotomy then says the
fiber trace is canonical almost everywhere, proving part 3.

