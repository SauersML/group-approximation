---
rg: 2
id: faithfully-traced-unital-coordinates-proof
kind: route
title: Polar correction, corner restriction, and almost-idempotent lifting
target: faithfully-traced-unital-coordinates
requires: []
artifacts:
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
---

## Direct proof

**1. Finiteness.**  If `v^*v=1` in `A`, then
`tau(1-vv^*)=tau(v^*v)-tau(vv^*)=0`; faithfulness gives `vv^*=1`.  For a norm
ultraproduct or norm corona, an isometry class has lifts `a_k` with
`a_k^*a_k->1` in the relevant operator-norm sense.  Polar correction gives
coordinate isometries `u_k=a_k(a_k^*a_k)^(-1/2)`, which are unitary by the
previous sentence, so the class is unitary.

**2. Corners.**  If `p!=0`, faithfulness gives `tau(p)>0`.  The normalized
restriction `tau_p(x)=tau(x)/tau(p)` on `pAp` is tracial and faithful.

**3. Projection lifting.**  A self-adjoint lift `x_k` of a corona projection
has `||x_k^2-x_k||->0`.  Functional calculus separates the two spectral
clusters near `0` and `1` and rounds `x_k` to projections `p_k` with
`||p_k-x_k||->0`.  Compressing arbitrary lifts shows

```text
p (prod A_k/directSum A_k) p
  ~= prod (p_k A_k p_k) / directSum (p_k A_k p_k).
```

End proof.

The old proof contained a fourth step claiming that for a finite von Neumann
algebra `M` the represented algebra `M or JMJ` is finite.  That step is false
for infinite factors and has been removed; it is precisely the error exposed
by the manuscript's constant-coordinate counterexample.
