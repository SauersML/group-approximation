---
rg: 2
id: chen-half-complexity-audit
kind: route
title: Import Chen's surface bounds and compare the punctured-sphere numbers
target: chen-half-complexity-does-not-force-injectivity
requires: [kl-cyclic-orbit-perfect-kernel]
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Citation import from Lvzhou Chen, *The Kervaire conjecture and the minimal
complexity of surfaces*, [author PDF](https://lvzhouchen.github.io/papers/kervaire.pdf),
read on 2026-08-24.

Corollary 6.5 states that for arbitrary `A` and a unimodular word in the free
HNN extension `A*Z`, every boundary-incompressible admissible surface has
`-chi >= deg/2`.  It strengthens the coefficient to `1-1/n` when every
nonidentity element of `A` has order at least `n`, so torsion-free gives
coefficient one.  Definition 5.1 identifies `n`-RF relative to the trivial
subgroup with order at least `n`; at `n=infinity` this is infinite order.
Theorem 5.3 and Corollary 5.4 give the local HNN version and coefficient
injectivity under the corresponding `infinity`-RF/RTF assumptions.

For a minimal identity with `k` conjugates, Chen's proof of Corollary 5.4
uses the punctured sphere with `-chi=k-1` and `deg=k`.  Substitution into the
unconditional coefficient `1/2` gives `k-1>=k/2`, which is no contradiction
for `k>=2`; substitution into coefficient one gives the contradiction
`k-1>=k`.

Finally `kl-cyclic-orbit-perfect-kernel` supplies the application here:
`N_m=A*<z>` and each `w_i` maps to `1` under the `z`-exponent homomorphism,
so each is unimodular in exactly Chen's free-HNN sense.
