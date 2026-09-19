---
rg: 2
id: anchored-all-pairs-finite-packets-have-zero-entropy
kind: claim
title: All-pairs finite-packet microstates with subquadratic exact class count are anchored entropy-null
artifacts:
  - research/artifacts/flexible-packet-anchoring-2026-08-22.md
distinct_from:
  anchored-exact-wreath-packets-have-zero-entropy: that excludes exact finite packet families; this excludes vanishing-defect all-pairs approximate representations by combining uniform finite-group HS stability with robust diffuse anchoring.
  finite-wreath-relative-tangent-moduli-vanish: that is infinitesimal near a fixed exact packet; this is global and nonlinear over the entire all-pairs approximate-representation space.
---

Let `G_n` be finite groups, `d_n->infinity`, `epsilon_n->0`, and let
`Phi_n` be a family of maps `f:G_n->U(d_n)` satisfying

```text
max_(g,h in G_n)||f(gh)-f(g)f(h)||_2<=epsilon_n.         (AFP6)
```

Fix a uniformly bounded number of output coordinates `F_n subset G_n`.
Assume every `f in Phi_n` has the same self-adjoint diffuse pin

```text
D_n=sum_(g in L_n) c_(g,n) f(g),
```

where the expression is self-adjoint and
`sum_g |c_(g,n)|<=C` uniformly.  Finally assume that, among all exact unitary
representations of `G_n` in dimensions

```text
d_n<=m<=d_n/(1-4epsilon_n^2),                            (AFP7)
```

the number of unitary-equivalence classes is `exp(o(d_n^2))`.

Then for every fixed `epsilon>0`,

```text
limsup_n d_n^(-2) log K_epsilon(
  {(f(g))_(g in F_n):f in Phi_n},||.||_2)=0.             (AFP8)
```

Hence a positive anchored entropy construction from growing finite packets
must fail at least one of three tests: all-pairs table defect must not vanish,
the exact representation classes must already have quadratic logarithmic
multiplicity, or the proposed anchor must fail to converge diffusely.
