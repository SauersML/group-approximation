---
rg: 2
id: stw22-diffuse-supercarrier-five-sphere-proof
kind: route
title: Bootstrap diffuse spectral supercarriers and stabilizers through degree five
target: stw22-diffuse-stiefel-uniform-five-sphere-fillings
requires:
  - stw22-diffuse-stiefel-uniform-four-sphere-fillings
artifacts:
  - research/artifacts/stw22-dim6-factor-bundle-breakthrough-2026-08-31.md
---

Projection orbit fibres are products of corner unitary groups.  Their
degree-three control lifts small projection `S^4` maps by controlled
Michael selection with `n=3`; the universal unitary `S^4` modulus fills
the lift.  Thus fixed-trace projection Grassmannians are four-connected and
uniformly equi-`LC^4`, including the translated values `P(h,q;s)` used by
the inclusive spectral construction after normalized-corner scaling.

For `x:S^5->Nq`, set `h_z=1_[kappa,infinity)(|x(z)|)` and
`s=2delta^2/kappa^2`.  The dimension-free lower-semicontinuity proof and
Michael with `n=4` select a constant-trace carrier `e_z` with

```text
tau(e_z)<=min(tau(q),s),       ||x(z)(q-e_z)||<=kappa.
```

Direct rotation localizes a small frame sphere to `q-e_z+w_z`.  The two
pair-conjugator multifunctions have corner-unitary stabilizers which are
four-connected and equi-`LC^4` by the degree-four Stiefel theorem.  Michael
with `n=4` selects their unitary `S^5` lifts.  Jekel contractions fill the
localized pair while every represented difference has right support
`e_z`, so the radius is at most `2sqrt(2)delta/kappa`.

With `epsilon_0=min(epsilon,1)`, `kappa=epsilon_0/40`, and
`delta=epsilon_0^2/1000000`, this and the direct-rotation collar lie in the
requested ball.  For an arbitrary frame sphere, Michael `n=4` lifts it to
`U(N)` and Jekel fills, proving global five-connectivity.

