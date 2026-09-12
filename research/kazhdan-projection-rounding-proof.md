---
rg: 2
id: kazhdan-projection-rounding-proof
kind: route
title: Kazhdan gap, bimodule identity, spectral rounding at one half
target: kazhdan-projection-rounding
requires: []
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

The action `Ad pi|_Gamma` on `L^2(M)` is trace preserving with fixed space
`L^2(N)`, and `||alpha_s(p)-p||_2=||[pi(s),p]||_2`, so property `(T)` bounds
the `L^2`-distance from `p` to `L^2(N)` -- realized by `E_N(p)` since `E_N` is
the orthogonal projection -- by `kappa^(-1)` times the commutator energy.
Writing `a=E_N(p)`, the bimodule and trace-preservation properties give
`tau(pa)=tau(a^2)` and `tau(a)=tau(p)`, so
`||p-a||_2^2=tau(p)-2tau(pa)+tau(a^2)=tau(a(1-a))` exactly.  Cutting `a` at
`1/2` inside `N` produces a projection `q` with
`||a-q||_2^2 <= 2 tau(a(1-a))`, because `(t-chi(t))^2 <= |t-chi(t)| <= 2t(1-t)`
on `[0,1]`.  Adding the two estimates gives the stated bound.  Complete
argument in the cited note, Proposition 11.
