---
rg: 2
id: sofic-action-gives-marked-pauli-central-product-microstates
kind: claim
title: Sofic action charts give marked microstates for the common-center Pauli lamp
artifacts:
  - research/artifacts/sofic-action-pauli-central-product-microstates-2026-08-30.md
distinct_from:
  gkp-wreath-permanence-theorem: that treats a restricted direct sum whose site groups have independent centers; this treats the quotient which identifies every site center with one marked involution, and so cannot follow from quotient closure of soficity.
  sofic-halo-products-preserve-hyperlinearity: that uses the halo intersection axiom; the Pauli packets on disjoint nonempty site sets here meet in the common mark, and the proof instead replicates that mark over all chart carriers.
  lamp-charts-recover-set-action: that recovers soficity of the underlying set action from lamp charts; this proves the forward construction once a sofic set action and a sofic actor are given.
  sofic-actor-refutes-lamp-character-transport: that records a marked falsifier for a special regular Tarski setup; this constructs the common-center Pauli microstates for every sofic set action.
---

Let a countable group `A` act on a countable set `X`, put

```text
V_X=direct_sum_X F_2,
P_X=V_X x V_X x F_2,
```

and multiply triples by

```text
(u,v,e)(u',v',e')
  =(u+u',v+v',e+e'+<v,u'>).                              (PCM1)
```

Write `J=(0,0,1)`.  If `A` is sofic and the set action `A action X` is
sofic, then

```text
P_X semidirect A                                         (PCM2)
```

is sofic.  There are sofic approximations of `(PCM2)` in which the Hamming
distance from `J` to the identity is exactly one at every stage.

More precisely, a finite sofic-action chart labels each requested finite
site window injectively on all but `o(1)` of its carriers.  Put one finite
Pauli group on the label set in every carrier, take their product, and map
`J` to the tuple of local central signs.  Label collisions and failed
covariance are the only Pauli multiplication errors and occupy `o(1)` of
the carriers.  The diagonal central tuple, by contrast, acts without fixed
points on every carrier.  An independent sofic approximation of `A`
supplies freeness on actor words.

For a transitive action and distinct `p,q in X`, the bare two-point seed

```text
<V_X semidirect A,z,J |
 z^2=J^2=1, J central, [delta_p+delta_q,z]=J>             (PCM3)
```

surjects onto `(PCM2)` by sending the lamps to the first Pauli coordinate
and `z` to the second-coordinate lamp at `p`.  This quotient preserves `J`.
Hence, when the actor and site action are sofic, no estimate inspecting only
a fixed finite window of the bare relations in `(PCM3)` can force every
approximate representation to send `J` to the identity.  For a recursive
presentation, the same obstruction applies to the usual pointwise-asymptotic
formulation after a diagonal choice of finite windows.

Applied to

```text
A=SL_3(Z[1/2]),       X=A/SL_3(Z),                        (PCM4)
```

the result is conditional because soficity of this dyadic building action
is open.  It says that a bare-seed `J`-collapse for `(PCM4)` would itself
prove that action nonsofic.  It does **not** establish or refute
`infinite-character-actor-word-energy-interface`: a viable packet may fail
either soficity hypothesis or use additional controller relations destroyed
by the quotient above.
