---
rg: 2
id: non-rf-hyperbolic-via-free-lamp-compression
kind: route
title: Replace commuting lamps by free lamps to make the compression witness hyperbolic
target: non-residually-finite-hyperbolic-group
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

The natural repair of `non-rf-hyperbolic-via-compression-transplant`.  What
obviously obstructs hyperbolicity of the compression witnesses is their large
abelian subgroups: the lamp coordinates commute, so `ℤ^2` or `(ℤ/2)^∞` sits
inside, and no hyperbolic group contains `ℤ^2`.  Replace the commuting lamp
group by a **free product** of finite lamp groups indexed by the coset space
`G/Γ`, with distinct coordinates in distinct free factors — this graph already
carries such an object (`free-lamp-radical-is-free`) — and the abelian
obstruction disappears.

Dead, and for the same reason as its parent, which is why the repair is worth
recording rather than trying.  Put `c = c_Γ` and `d = tct^(-1) = c_(tΓ)`, and
pick `γ ∈ Γ ∖ tΓt^(-1)`, which exists because the compression is strict.  Then
`γ t Γ ≠ t Γ`, so `γ d γ^(-1) = c_(γtΓ)` is a nontrivial element of a
*different* free factor from `d`, and in a free product of nontrivial groups
two such elements do not commute:

```text
[d, γ] != 1.
```

But `hyperbolic-compression-centralizer-rigidity` forces `d ∈ C_G(Γ)` whenever
the ambient group is hyperbolic and `Γ` is non-elementary, giving `[d,γ] = 1`.
So the free-lamp configuration and hyperbolicity of the ambient group are
incompatible outright — the lamps are not merely a hyperbolicity obstruction
to be engineered away, they are the thing the rigidity theorem forbids.

**What survives the demolition.**  Free lamps remain the right move for every
purpose in this program that is not hyperbolicity: they are what makes the
radical free and the coordinate action faithful.  What dies is the reading of
"remove the `ℤ^2`" as the only obstacle between the compression architecture
and a hyperbolic example.
