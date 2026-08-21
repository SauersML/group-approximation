---
rg: 2
id: trace-zero-involution-projective-transfer-equivalence-proof
kind: route
title: Dilate a relative-commutant leak to a trace-zero involution
target: trace-zero-involution-projective-transfer-equals-rcc
requires:
  - projective-transfer-equals-rcc-for-perfect-pairs
---

Write `a=pi(h)` and amplify `pi` diagonally:

```text
pi_2(g)=diag(pi(g),pi(g)).
```

For `u in pi(C)'` put

```text
v = [[0,u],[u*,0]].                                    (DIL1)
```

Then

```text
v*=v,       v^2=1,       tau_2(v)=0,
v in pi_2(C)'.                                         (DIL2)
```

A direct multiplication gives

```text
[v,pi_2(h)]
 = diag(u a u* a*, u* a u a*).                        (DIL3)
```

Put

```text
r=|tau(u a u* a*)|.
```

The second diagonal block in `(DIL3)` is unitary, so its trace has modulus
at most one.  Therefore

```text
|tau_2([v,pi_2(h)])| <= (r+1)/2.                       (DIL4)
```

If `e(u,a)>=epsilon`, then `r<=sqrt(1-epsilon)`, and `(DIL4)` yields
exactly `(TZI1)`.  In particular the dilated commutator cannot be scalar.

This proves that failure of ordinary relative-commutant collapse produces a
failure witnessed by a trace-zero involution.  The reverse implication is
immediate because involutions are unitaries.  Finally
`projective-transfer-equals-rcc-for-perfect-pairs` removes scalar phases on
`C` and then on `A`, proving the three-way equivalence.

The same argument applies to sequences.  If the original leak has
`liminf e(u_n,pi_n(h))>=epsilon`, its dilations have
`liminf e(v_n,pi_{2,n}(h))>=Phi(epsilon)`.  Ordinary asymptotic centrality
on `C` is preserved exactly by `(DIL1)`; for projective centrality on a
perfect `C`, the phase characters first converge to the trivial character,
after which the same conclusion holds.
