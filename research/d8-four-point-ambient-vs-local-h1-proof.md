---
rg: 2
id: d8-four-point-ambient-vs-local-h1-proof
kind: route
title: Separate ambient and short-edge coboundaries on a four-point D8 cloud
target: ambient-h1-triviality-need-not-be-short-edge-local
requires: []
artifacts:
  - research/artifacts/d8-ambient-local-h1-firewall-2026-08-30.md
---

Let `B=D8`, `A=<r^2,s>`, and `alpha=Ad(s)` as in the claim.

The subgroup `A` is abelian, and `alpha` fixes both of its generators.
Therefore every `A`-valued coboundary

```text
a^(-1) alpha(a)
```

is trivial, while `z(q)=r^2` is a cocycle because
`r^2 alpha(r^2)=1`.  Hence `[z]` is nontrivial in `H^1(C2,A)`.

In `B`,

```text
r^(-1) alpha(r)
 = r^(-1) s r s
 = r^(-1) r^(-1)
 = r^2,
```

so `[z]` becomes trivial in `H^1(C2,B)`.

Write an arbitrary element of `B` as `r^k` or `r^k s`.  Directly,

```text
(r^k)^(-1) alpha(r^k)=r^(-2k),
(r^k s)^(-1) alpha(r^k s)=r^(2k).
```

Either expression equals `r^2` exactly when `k` is odd.  Thus every
trivializing cochain is one of

```text
r, r^3, rs, r^3s.
```

For the displayed cloud, every element of `A` preserves each of the two
diameter-`2 sin(theta)` clusters.  Every odd-`r` element exchanges those
clusters, which lie in orthogonal two-planes, so its displacement is exactly
`sqrt(2)`.  Letting `theta->0` proves the quantitative assertion.
