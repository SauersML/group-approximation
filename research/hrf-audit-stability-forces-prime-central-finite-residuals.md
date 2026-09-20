---
rg: 2
id: hrf-audit-stability-forces-prime-central-finite-residuals
kind: claim
title: Flexible HS stability forces almost every prime reduction of a Kazhdan integral central cover to have invisible central kernel
distinct_from:
  kazhdan-hyperbolic-hs-stability-kills-hyperlinearity: that uses Dogon--Vigdorovich to produce one nonhyperlinear finite central extension; this uses finite quotient representations and a Kazhdan intertwiner to put the entire prime central kernel in the finite residual for all but finitely many primes, without claiming nonhyperlinearity.
  hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class: that assumes hyperlinearity and obtains a persistent prime class after passing to finite index; this needs no hyperlinearity and obtains persistence for all but finitely many reductions of each specified integral central cover.
artifacts:
  - research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md
---

**ESTABLISHED as a conditional theorem; it supplies no instance of the stability hypothesis.**

Let `Gamma` be finitely generated and flexibly HS-stable, and let

```
1 -> <z> = Z -> E -> Gamma -> 1
```

be a central extension such that `E` has property (T). There is an integer `M >= 1`
such that every finite quotient of `E` kills `z^M`. Consequently:

1. For every prime `p` not dividing `M`, the entire central subgroup `C_p` of
   `E_p = E/<z^p>` lies in the finite residual of `E_p`. In particular `E_p` is not
   residually finite.
2. If `c in H^2(Gamma;Z)` is the extension class, its reduction `c_p` is nonzero on
   every finite-index subgroup of `Gamma` for every such prime.
3. If `Gamma` is word-hyperbolic, every `E_p` is word-hyperbolic. Thus one flexibly
   HS-stable hyperbolic Kazhdan group with `b_2(Gamma;Q)>0` suffices for a
   non-residually-finite hyperbolic group by this argument alone.

In item 3 the integral cover can be chosen to have finite abelianization by
universal coefficients and the homology five-term sequence, and is Kazhdan by
Bekka--de la Harpe--Valette. No nonhyperlinearity conclusion is asserted here.
The proof is an elementary specialization of the central-projective instability
mechanism already recorded in Cairn; no new-priority claim is made.

DERIVATION
hrf-audit-stability-prime-central-finite-residuals-proof
