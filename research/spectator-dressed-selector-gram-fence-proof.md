---
rg: 2
id: spectator-dressed-selector-gram-fence-proof
kind: route
title: Separate conjugator dressing from target dressing and build the tensor spectator
target: spectator-dressed-gram-does-not-share-selector-gauges
requires:
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - root-valued-overlap-does-not-undress-external-selector
  - packet-dressed-shared-implementer-requires-one-outer-class
---

Equation `(SDG2)` follows immediately from `[H,R]=1`.  Equation `(SDG3)`
is tensor multiplication, and the affine rank formula shows why it is not
the same selector target unless an additional rank equality is proved.

For the finite model take diagonal involutions `V_1,V_2` on `C^12` with
positive ranks `6,10`.  On the computational basis of `C^8`, let `C_1` be
negative on two basis vectors and `C_2` negative on one.  Counting signs in
the tensor products gives

```text
rank_-(C_1 tensor V_1)=48=96/2,
rank_-(C_2 tensor V_2)=24=96/4.                         (1)
```

Every three-qubit primal translation and dual character acts on the first
tensor factor, while `H_i=I_8 tensor V_i` acts on the second.  Hence all
their commutators are one.  Since `V_i^2=1`,

```text
H_i(C_i tensor V_i)=C_i tensor 1.                      (2)
```

The two label-stripped dressed words in `(2)` are both the identity on the
reservoir, so their cross-Gram support is the full `96`-dimensional carrier.
But positive rank is invariant under unitary conjugacy, and `6!=10`, so
`V_1,V_2` are not conjugate.  The MSI-only signed-permutation audit checks
the six primal/dual Pauli commutations, both affine ranks, both legitimate
conjugator dressings, the dressed-word cancellation and full cross Gram.

