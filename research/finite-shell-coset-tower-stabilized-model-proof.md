---
rg: 2
id: finite-shell-coset-tower-stabilized-model-proof
kind: route
title: Convert a fundamental atom to a coset PVM and stabilize it regularly
target: finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift
requires:
  - native-sl3-edge-parahoric-has-index-forty-two
  - native-sl3-group-is-hecke-graph-wreath-product
  - coset-tower-hybrid-reflection-pays-exact-payload-leakage
---

The shell action of `C` factors through

```text
Q=C/core_C(D),                 H=D/core_C(D).
```

The first prerequisite gives `[Q:H]=[C:D]=42`.  Suppose first that `E`
satisfies `(FST2)`.  For an atom of `l_infinity(Q/H)` define

```text
Phi(1_(gH))=alpha_g(E).                                (1)
```

`H`-invariance makes `(1)` independent of the representative.  The
orthogonality and coverage identities in `(FST2)` say exactly that `(1)`
extends to a unital star homomorphism, and its definition makes it
`Q`-equivariant.  Each atom is nonzero, so the homomorphism is injective.
Conversely, evaluating any unital equivariant embedding at `1_H` gives
`(FST2)`.  Trace invariance makes the 42 translates equitracial, and their
sum is one, hence

```text
tau(E)=1/42.                                           (2)
```

Let `pi` be the permutation representation of `Q` on `l^2(Q/H)`.  For

```text
beta_g=alpha_g tensor Ad(pi(g)),
E_tilde=1 tensor |delta_H><delta_H|,
```

every `h in H` fixes `E_tilde`, while its translate indexed by `gH` is

```text
1 tensor |delta_(gH)><delta_(gH)|.
```

These 42 projections are pairwise orthogonal and sum to one.  This proves
the exact stabilized tower.  If `p` is a nonzero invariant carrier, the
same calculation with `p tensor |delta_H><delta_H|` takes place in the
corner whose unit is `p tensor 1`.

The second prerequisite identifies the native shell lamps with distinct
graph-product generators.  Thus in

```text
L^2(M)=l^2(W_S)
```

the vectors `lambda(c_(ga))`, indexed by `gH`, are distinct group-basis
vectors and hence orthonormal.  The shell action permutes them by left
translation, and the stabilizer of the base vector is exactly `H`.
Their span is therefore a copy of the quasi-regular module `l^2(Q/H)`
inside the unamplified Koopman representation.  The necessary linear
character datum is already present; turning those vectors into projections
with the multiplication table `(FST2)` is the additional nonlinear step.

A stand-alone finite role packet realizes the preceding matrix construction
in a chosen representation, but its group multiplication relations do not
select that representation type or its rank-one atom in every
representation.  It therefore proves stabilized existence, not descent of
the coordinate atom to `M`.  Nor would an unstabilized PVM alone authenticate
the payload: by the leakage prerequisite, for assigned reflections `A_i`
its hybrid compression satisfies

```text
tau(1-(sum_i E_iA_iE_i)^2)
   =1/2 sum_i ||[E_i,A_i]||_2^2.                       (3)
```

Thus payload reduction is a separate commuting-square condition.  This
route proves only the equivalence `(FST1)--(FST2)`, the regular stabilized
model, and the absence of a linear representation obstruction.  It neither
constructs nor rules out the unstabilized embedding
`l_infinity(Q/H)->L(W_S)`, and it supplies no ordinary-word payload
authenticator.
