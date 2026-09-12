---
rg: 2
id: returned-a2-same-cut-pauli-free-proof
kind: route
title: Finite cyclic-packet proof that the returned A2 word leaves both Pauli rows free
target: returned-a2-window-leaves-same-cut-pauli-commutators-free
requires:
  - returned-opposite-cross-zero-has-finite-s6-model
---

Let `B` be the finite returned packet in
`returned-opposite-cross-zero-has-finite-s6-model`.  Take three coordinate
copies and let `c` cyclically permute them.  The finite semidirect product

```text
B^3 semidirect <c>,                 c^3=1,             (RPP1)
```

is exactly the construction used there to adjoin the full relative `A_2`
occurrence orbit: the literal relative word `V` is represented by `c`, the
child/parent Whitehead and returned cross-zero rows hold coordinatewise,
and the third relative step returns every named occurrence.

Now let

```text
P=<X,Z,J | X^2=Z^2=J^2=1, J central, XZ=JZX>          (RPP2)
```

be the order-eight Pauli group.  Adjoin three packet copies `P_0,P_1,P_2`
and let the same `c` cyclically permute their indices.  Thus the full finite
model is

```text
G=(B^3 times P_0 times P_1 times P_2) semidirect <c>. (RPP3)
```

This is a legitimate extension of the returned-window model: all old words
retain their `B^3 semidirect <c>` values, all packet-local relations hold in
the corresponding `P_i`, and the relative orbit transports packet `i` to
packet `i+1`.  No old row identifies two different packet copies; that
identification is exactly the proposed new mixed commutator row.

Write `X_i,Z_i,J_i` for the generators of `P_i` and work in the left regular
representation of `G`.  Put

```text
E=prod_(i=0)^2 (1-J_i)/2.                              (RPP4)
```

The `J_i` are commuting central involutions in the base group and `c`
permutes them, so `E` is central in `C[G]` and commutes with `V=c`.
Expansion of `(RPP4)` shows that the identity coefficient of `E` is `1/8`;
hence its canonical trace is `1/8`.  On `EH`, every `J_i` acts as `-1`, so
in particular

```text
X_0Z_0E=-Z_0X_0E.                                     (RPP5)
```

The same literal relative word transports the two generators:

```text
VX_0V^*=X_1,                  VZ_0V^*=Z_1.             (RPP6)
```

Normalize the corner trace by `tau_E(T)=tau(ET)/tau(E)`.  No term in the
expansion of `E X_1X_0` is the identity: multiplication by a product of the
central `J_i` cannot cancel the two noncentral Pauli letters.  Therefore

```text
tau_E(X_1X_0)=0.                                      (RPP7)
```

The same argument gives `tau_E(Z_1Z_0)=0`.  Since all four Pauli letters are
self-adjoint involutions, `(RPP6)--(RPP7)` yield

```text
||[V,X_0]E||_(2,E)^2
 =||V X_0 V^*-X_0||_(2,E)^2
 =||X_1-X_0||_(2,E)^2=2,

||[V,Z_0]E||_(2,E)^2=2.                               (RPP8)
```

Thus the source Pauli pair is exposed on one literal, positive,
`V`-invariant finite-coordinate cut, yet both desired mixed commutators have
maximal regular-trace defect.  Because every hypothesized premise is exact,
any normal-closure derivation of either commutator from the returned window
would also hold in `G`, contradicting `(RPP8)`.
