---
rg: 2
id: fixed-shift-invariance-does-not-force-flat-profile
kind: claim
title: Fixed-shift invariance on growing scale lattices does not force a flat profile
invalidates:
  - lambda-exact-p-three-closure-route
artifacts:
  - research/artifacts/sl3-projective-rcc-audit-2026-08-21.md
distinct_from:
  parabolic-spectrum-is-doubling-invariant: that concerns exact invariance of a spectral measure under a fixed expanding map; this claim concerns asymptotic translation invariance on growing finite lattices.
  lambda-exact-face-of-the-collapse-closes: that contains the attempted flat-profile inference invalidated here; the preceding min-overlap/Folner conclusion may remain valid.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that is a conditional producer of an RCC counterexample; this is an unconditional counterexample to one profile-rigidity inference only.
---

There are probability measures on growing one- and two-dimensional cyclic
scale lattices that are asymptotically invariant in total variation under
every fixed translation, have vanishing largest atom, and nevertheless stay
a fixed positive total-variation distance from Haar measure.

Concretely, on `Z/(N+1)Z`, represented by `0,...,N`, put

```text
c_N = 2/((N+1)(N+2)),       mu_N(k) = c_N (k+1).
```

Then for every fixed integer `r`,

```text
TV(mu_N, shift_r(mu_N)) -> 0,
max_k mu_N(k) -> 0,
```

but, for the uniform probability `u_N`,

```text
TV(mu_N,u_N) -> 1/4.
```

The product measures `nu_N=mu_N tensor mu_N` have the same properties on
the two-dimensional tori: invariance under every fixed coweight translation
and vanishing atoms do not imply convergence to Haar. Therefore the
fixed-shift conclusion supplied by the min-overlap argument is a Folner or
delocalization statement, not a unique-flat-profile theorem. Any closure of
the spread sector needs an additional multiscale regularity, entropy, or
expansion input.

