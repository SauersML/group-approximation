---
rg: 2
id: finite-group-actions-have-coherent-same-cloud-shadows
kind: claim
title: Faithful finite-group actions admit coherent shadows on the same spherical cloud
distinct_from:
  coherent-reselection-reduces-to-private-label-core: that peels relation systems with fresh labels; this handles a genuinely closed, nonempty relation core by balancing complete finite-group orbits.
  orbit-transport-gauge-needs-a-closed-label-set: that reduces a closed table to an unproved near-orbit packing for independently chosen matchings; this constructs the coherent maps directly from an equivariant measurable partition.
  local-source-gauge-is-coherent-shadow-reselection: that is a change of variables; this is an independent existence theorem for a nontrivial subclass.
---

Let `K` be a finite group and let

```text
V:K -> U(H)
```

be a faithful unitary representation on a finite-dimensional Hilbert space.
Let `x_1,...,x_N` be iid uniform points on the unit sphere of `H`.  For
every `rho>0`, with probability tending to one as `N` tends to infinity
there is an exact action

```text
tau:K -> Sym(N)
```

such that, simultaneously for every `s in K`,

```text
|{i: norm(x_(tau_s(i))-V_s x_i)>rho}|=o(N).             (FGS1)
```

Moreover, distinct elements of `K` disagree on `1-o(1)` of the roots.
Thus the complete multiplication table of `K`, including its nonempty
closing relation core, has coherent permutation shadows on the same cloud.

The conclusion is stable under normalized-Hilbert--Schmidt perturbation.
If unitaries `U_s` on `H` satisfy

```text
norm(U_s-V_s)_2 <= kappa_s,
```

then for every `t>0` the same permutations satisfy, with probability
tending to one,

```text
|{i: norm(x_(tau_s(i))-U_s x_i)>rho+t}|/N
  <= kappa_s^2/t^2+o(1).                               (FGS2)
```

Consequently, any sequence of finite-group regular-character microstates
which is normalized-HS close to exact faithful representations admits
coherent same-cloud reselection with shadow radius and exceptional density
tending to zero, after taking each cloud sufficiently large.

This is a direct orbit construction.  It neither starts from independent
shadow permutations nor assumes the local gauge conclusion.

**ESTABLISHED.**

DERIVATION
[[finite-equivariant-cell-shadow-proof]]
