---
rg: 2
id: regular-iwahori-edge-types-have-moving-power-charge
kind: claim
title: Regular Iwahori edge types retain a moving power charge against sublinear padding
distinct_from:
  iwahori-edge-restriction-image-has-continuous-type: that exhibits a continuum of fixed two-dimensional edge types; this tensor-regularizes that family and proves the continuum remains visible to a moving kernel word even when the fixed-word character is regular.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that preserves a hypothetical projection-transfer failure under regular tensor camouflage; this gives an unconditional explicit family and a stable-equivalence obstruction for the edge representations themselves.
  finite-graph-of-groups-representation-types-are-integer-flows: that rounds a fixed finite-rank restriction module when edge groups are finite; this proves regular trace and `o(d)` padding do not manufacture such a module for the infinite Iwahori edge.
  cuspidal-redistribution-refutes-regular-core-orbit-basin: that keeps the core restriction exactly fixed while changing a positive-density global congruence type; this changes nearby continuous edge types and proves fixed-type padding cannot match them.
---

Let

```text
V=PSL_2(Z)=<x,a | x^2=a^3=1>,
H=Gamma_0(2)/{+-I}=<t,w | w^2=1>,
t=xa.                                                  (RPC1)
```

There are pairs of exact vertex representations

```text
sigma_n,tau_n:V -> U(D_n)                             (RPC2)
```

with the following properties.

1. Both normalized characters converge pointwise to the regular character
   of `V`, and their restrictions have the regular limiting character of
   `H`.
2. On a fixed generating set of `H`,

   ```text
   max_(s in {t,w})||sigma_n(s)-tau_n(s)||_2=O(1/m_n)->0. (RPC3)
   ```

3. Nevertheless no representations `eta_n,zeta_n` of `H` with

   ```text
   (dim eta_n+dim zeta_n)/D_n ->0                     (RPC4)
   ```

   can make

   ```text
   sigma_n|H direct-sum eta_n
      ~= tau_n|H direct-sum zeta_n.                   (RPC5)
   ```

Thus regular-character restriction plus sublinear padding does **not** turn
the infinite edge into the finite-rank Gerasimova--Shchepin integer-flow
setting.  Two edge types can be arbitrarily close on every fixed edge
generator while a moving kernel word detects a macroscopic stable type
charge.

This is not a counterexample to flexible Iwahori stability.  The two vertex
representations in `(RPC2)` are themselves `O(1/m_n)`-close and may be made
equal by changing their continuous angle.  The result instead rules out a
direct extension of the finite-edge proof which freezes vertex types and
repairs incompatibility only by matching irreducible multiplicities and
adding `o(d)` dimensions.  A successful infinite-edge theorem must use
analytic motion inside the continuous modular representation variety.

Nor may that analytic motion be targeted at one preselected regular-quotient
endpoint type.  `cuspidal-redistribution-refutes-regular-core-orbit-basin`
keeps an authenticated core restriction literally unchanged while
redistributing a positive-density cuspidal global type; both global
characters remain asymptotically regular.  The valid target must therefore
be adaptive in two independent senses: move continuous vertex parameters
and choose the global endpoint representation type from the full restriction
fiber.
