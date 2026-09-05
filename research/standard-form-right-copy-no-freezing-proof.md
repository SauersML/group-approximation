---
rg: 2
id: standard-form-right-copy-no-freezing-proof
kind: route
title: Compute the failed cross-commutator, the nontracial mixed state, and the moved readable atom
target: standard-form-right-copy-does-not-freeze-zpc-controls
requires: []
artifacts:
  - experiments/standard_form_right_copy_no_freezing.py
---

Three exact calculations, all inside `M_2(C)` on `L^2(M,tau)`.

## 1. The mixed vector state is not a trace

The obstruction can be seen without naming the second player.  The vector
functional

```text
phi(L(x)R(y)) = tau(xy)                                  (SFR3)
```

on `W*(L(B),R(A))` need not be tracial.  Take the normalized trace on
`M=M_2(C)` and the Pauli matrices

```text
X = [[0,1],[1,0]],
Y = [[0,-i],[i,0]],
Z = [[1,0],[0,-1]].
```

Let `A=W*(Z)` and `B=M_2(C)=W*(X,Y)`.  The two unitaries

```text
S=L(X),                     T=L(Y)R(Z)
```

belong to the mixed algebra.  Since `XY=iZ` and `YX=-iZ`,

```text
phi(ST)=tau(i Z^2)= i,
phi(TS)=tau(-i Z^2)=-i.                                (SFR4)
```

So `phi` is not tracial, and the usual synchronous/tracial passage from one
observable family to commuting Alice and Bob copies cannot be applied after
the switch.

## 2. A relation can hold on the selected vector and fail on its hull

Put `p=(1+Z)/2=e_11`.  Then

```text
(Z-1)p=0.                                               (SFR5)
```

So the left observable `L(Z)` fixes the selected vector `R(p)Omega=p`.  It
is not the identity on the right ideal `R(p)L^2(M)`: for `xi=e_21`,

```text
R(p)xi=xi,                  L(Z)xi=-xi.                 (SFR6)
```

Scalar compression of a frozen relator at the trace vector therefore does
not make that relator an operator identity on the cyclic space once remote
unreadable operators move the readable atom.  This is the standard-form
version of the normal-ideal failure already isolated by
`scalar-relator-compression-does-not-kill-normal-ideal`.

## 3. Magic-square realization

In `finite-magic-square-selector-has-no-frozen-branch` the readable selector
is `e=Z tensor I`, while the remote unreadable `a=X tensor I` satisfies

```text
[a,e]=J.
```

The readable atoms are moved by `a`.  A right-action copy of their
projections commutes with Alice's left copy of `a`, but not with Bob's right
copy.  If it did yield a commuting frozen strategy, freezing either selector
value would make `e` a central scalar, forcing simultaneously `[a,e]=1` and
`[a,e]=J`, hence `J=1`.  The exact Pauli strategy has `J=-1`, so this is
impossible.

The general calculation `(SFR2)` in the target claim identifies the failed
commutator before the magic-square contradiction is invoked, so the no-go
does not depend on that particular game.  All of `(SFR1)`--`(SFR6)` and the
selector contradiction are replayed in exact Gaussian-rational arithmetic by
`experiments/standard_form_right_copy_no_freezing.py`.
