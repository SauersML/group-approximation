---
rg: 2
id: local-or-simulation-has-linear-normalized-loss
kind: claim
title: A normalized local simulation of tensor OR pays linear loss at bounded encoding depth
artifacts:
  - research/artifacts/local-or-simulation-loss-2026-09-12.md
distinct_from:
  global-walk-reducer-has-net-energy-gain: that asks only for ground-energy bounds after a general instance-level reduction; this bounds the stronger statewise simulation of one tensor-OR clause under a specified local encoding.
---

Let `P_t=I-|0^t><0^t|` on `t` data qubits. Append any fixed pure ancilla
state `a`, independent of the data, and encode by a depth-`D` circuit `U`
of disjoint gates of arity at most `b>=2` in each layer:
`V psi=U(psi tensor a)`. Let

```text
K=sum_i p_i k_i,   p_i>=0, sum_i p_i=1,
0<=k_i<=I,   |support(k_i)|<=k,
eta=<V0^t,K V0^t>.
```

No commutation, degree, geometry, or ancilla-product assumption is made.
If `L>0`, `delta>=0`, and the operator inequality

```text
V* K V >= P_t/L - delta I
```

holds, then

```text
1/L <= eta+delta+min{1,k b^D/t}.
```

In particular, exact vacuum preservation and exact statewise domination
force `L>=t/(k b^D)` whenever `k b^D<=t`. For `D=0`, no ancillas and
`1<=k<=t`, the optimal loss is exactly `t/k`, achieved by the uniform
average of the `k`-site OR projectors.

Consequently, at fixed `k,b,D`, a family of such simulators with
`eta+delta=o(1/t)` cannot have `L_t=o(t)`. This excludes bounded-depth
faithful clausewise simulation as a way to obtain sublinear tensor-walk
reduction loss. The general ground-energy-only reducer remains open.
