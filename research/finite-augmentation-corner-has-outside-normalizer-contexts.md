---
rg: 2
id: finite-augmentation-corner-has-outside-normalizer-contexts
kind: claim
title: A full finite augmentation corner admits an explicit noncommuting two-context transport outside its subgroup normalizer
distinct_from:
  noncentral-frobenius-negative-corner-is-rational-matrix-algebra: that supplies a local finite matrix block and proper literal partial transports; this combines transported pieces into a finite-support corner unitary with support outside every finite subgroup.
  common-corner-literal-contexts-stop-at-bass-serre: that classifies single literal corner-unitary transport; this uses an explicit sum of orthogonal partial transports and verifies a common two-context PVM.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes a complete no-CE atlas confined to one finite root block; this gives a small consistent diagram whose displayed supports escape every finite subgroup, while recording its remaining finite-dimensional algebra and finite-window host obstruction.
artifacts:
  - research/artifacts/finite-augmentation-outside-normalizer-two-context-cell-2026-09-08.md
---

Let `G=A_4 wr Z`, let `t` shift its finite lamps, and let
`J_i=t^i J_0 t^(-i)` be their double transpositions. Set

```text
q_i=(1-J_i)/2,
K=<J_0>,       q=q_0=1-e_K,
f=q_-1 q_0(1-q_1),
r=t f t^(-1)=q_0 q_1(1-q_2),
v=t f,
S=q-f-r,
P_+=(f+r+v+v^*)/2,
P_-=(f+r-v-v^*)/2.
```

Then `(S,f,r)` and `(S,P_+,P_-)` are exact rational
three-outcome PVMs in `q Q[G]q`, with the same unit and
the same nonzero proper atom `S`. Moreover,

```text
R=S+(f+r+v-v^*)/sqrt(2)
```

is a finite-support unitary of the `q` corner which sends
the first PVM to the second, and `||[f,P_+]||=1/2`.
A rational rotation gives the same construction with a rational
transport unitary and commutator norm `12/25`.

The supports of `P_+,P_-` and `R` contain elements outside
`N_G(K)` and are contained in no finite subgroup of `G`.
Their normalized corner probabilities are `(1/2,1/4,1/4)`.
Thus this is an actual finite-support transport beyond the
literal normalizer case.

Its scope is limited: the two PVMs together generate
`M_2(C) direct-sum C`, and every finite algebraic corner
diagram in this wreath-product host has a finite-window model
in a finite group retaining `J_0`. Consequently the host admits
no completed `B_loop` map with this nonzero corner unit.

DERIVATION
finite-augmentation-wreath-partial-rotation-proof
