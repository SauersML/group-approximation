---
rg: 2
id: jacobson-property-t-and-finite-k-do-not-exactify-the-head
kind: claim
title: Property T and exact finite qutrit packets stop strictly before Jacobson head exactification
artifacts:
  - research/jacobson-relative-hs-rigidity-firewall-proof.md
distinct_from:
  binary-jacobson-core-is-weakly-sofic-with-fd-head-radical: that proves every exact finite-dimensional representation kills the finitary kernel; this identifies the missing uniform-in-dimension continuity needed to pass from approximate to exact representations.
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for a representation-dependent same-square decoder; this proves that property T, finite-packet exactification and the known Frobenius stability theorems do not supply its operator-norm occurrence.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for one calibrated mixed S/T return; this shows why a finite K-type or relative-T argument cannot replace that mixed occurrence.
---

**ESTABLISHED FIREWALL.**  Let

```text
G=EL_28(F_2<S,T | TS=1>),
L=ker(G->EL_28(F_2[z,z^(-1)])),
K=GL_28(F_2),
w=x_13(1-ST).
```

Then `G` has Kazhdan property `(T)`, so the pair `(G,L)` has
relative property `(T)`.  Nevertheless none of the following established
inputs implies that normalized-Hilbert--Schmidt microstates kill `w`:

1. property `(T)` or relative property `(T)`;
2. the property-T proof by root-system grading and relative root estimates;
3. 2-Kazhdan/Frobenius stability in the unnormalized Frobenius norm;
4. exactification of the fixed finite group `K`;
5. finite-dimensional annihilation of `L`;
6. finite normal generation or finitary-root commutator identities.

The exact missing assertion is the dimension-free head modulus.  For a fixed
finite presentation `<S | R>` and the fixed word `w`, put

```text
kappa_w(delta)
 = sup ||w(U)-I||_(2,n),                                (JRF1)
```

where the supremum runs over all dimensions and all unitary `S`-tuples
with every relator defect at most `delta` in normalized HS norm.  What is
needed is

```text
lim_(delta->0) kappa_w(delta)=0.                         (JRF2)
```

Statement `(JRF2)` is equivalent to saying that every homomorphism from
`G` to a normalized-HS matrix ultraproduct kills `w`.  It is therefore
the head HS-ultraproduct-invisibility target itself, not a consequence of
property `(T)`.

There are two sharp reasons the standard rigidity inputs stop.

First, a relator can be `o(1)` in normalized HS norm while its adjoint
action on the HS Hilbert space stays distance two from the identity.  Thus
an approximate matrix representation does not produce the genuine unitary
representation to which relative property `(T)` applies.

Second, every finite head window is compatible with the exact qutrit packet.
For every finite `E subset L`, closing `E` under the finite `K)-orbit
produces a finite subgroup

```text
<K,E>.
```

Its regular representation is an exact finite-dimensional model of all
relations internal to that window, in which every nonidentity element has
canonical trace zero.  In particular the head involution has a negative cut
of density one half.  Hence exact `K)-types, all qutrit spectral marginals,
and any fixed finite collection of finitary head roots have an exact
head-retaining model.

A successful contradiction must therefore use a calibrated mixed
`S/T)-bearing actor occurrence which couples different finite head
windows.  It cannot follow from finite `K)-exactification, relative
property `(T)), or unnormalized Frobenius stability alone.
