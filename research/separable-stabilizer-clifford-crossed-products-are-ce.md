---
rg: 2
id: separable-stabilizer-clifford-crossed-products-are-ce
kind: claim
title: Clifford crossed products of residually finite actions with separable stabilizers are Connes embeddable
distinct_from:
  positive-core-bernoulli-ce: that obtains Connes embeddability of a commutative Bernoulli crossed product through soficity of a positive sub-action and wreath permanence; this is the anticommuting Clifford base, where there is no wreath group to be sofic, and it gets exact finite-dimensional moment models directly from finite quotients.
  profinitely-saturated-clifford-covers-are-surjunctive: that proves surjunctivity of Clifford cover groups from profinite separation of sites; this proves Connes embeddability of the tracial Clifford crossed product under stabilizer separability, a different conclusion about a different object.
  gkp-sofic-action-toolkit: that is the permanence toolkit for sofic actions on countable sets; this is an operator-algebraic embedding theorem for Bogoliubov crossed products, and it needs exact finite quotients rather than approximate sofic charts.
artifacts:
  - research/artifacts/kt-amenable-compressor-clifford-ce-2026-09-16.md
---

Let `H` be a countable residually finite group and `X` a countable `H`-set
such that every point stabilizer `H_x` is separable in `H`:

```text
H_x = intersection over finite-index normal N <| H of  H_x N.
```

Let `Cl(X)` be the tracial Clifford von Neumann algebra on self-adjoint
unitaries `c_x` with `c_x c_y = -c_y c_x` for `x != y`, and let `H` act by
the Bogoliubov automorphisms `c_x |-> c_{hx}`.  Then

```text
Cl(X) rtimes H,       tau(a u_h) = tau(a) delta_{h,e},
```

is Connes embeddable.

For every finite window of generators and every moment length, the proof
supplies a finite-dimensional model `Cl(Y) rtimes (H/N)` whose moments agree
with those of `Cl(X) rtimes H` **exactly**.  Here `Y` is a finite quotient
set of the relevant orbits.  The mechanism is that a Clifford word's trace
depends only on the equality pattern of its labels and on whether its group
part is trivial.  Finite quotients preserve both on a finite window by
separability and residual finiteness.

The hypotheses pass to subgroups `K <= H`.  They hold for free actions of
residually finite groups.  They fail for `G action G/Gamma` whenever
`Gamma` is infranormal and not normal (`infranormal-compact-closure-normal`).
This is why the theorem is applied to the Kun--Thom base `Gamma`, never to
the ambient group.

DERIVATION
separable-stabilizer-clifford-ce-proof
