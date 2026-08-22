# The recursive kernel family stays in finite packet groups

Write `H=<u,v> congruent S_3` for the constant `GL_2(F_2)` subgroup inside
`R^x`, and `delta` for the scalar self-embedding.  The basic matrix identity
behind `leavitt-matrix-amplification-in-unit-group-algebra` says

```text
[H,delta(R^x)]=1.
```

It propagates to every pair of distinct layers: for `i<j`, apply `delta^i` to
`[H,delta^(j-i)(H)]=1`.  Hence

```text
H_n=<delta^i(H):0<=i<=n>
```

is a quotient of `H^(n+1)`, in particular finite with order at most
`6^(n+1)`.

The seed `z=[1]+[g]+[g^2]` and the corner idempotent
`f=[1]+[u]+[v]+[g]` are both supported in `H`.  Since
`lambda(a)=delta_*(a)f`, support in `H_n` moves to support in `H_(n+1)`.
Therefore `q_n=lambda^n(z)` lies in `F_2[H_n]`.

This gives a precise boundary for the recursive correction idea.  The family
is infinite and orthogonal only because the finite packet group grows with
the depth.  Every actual group-algebra expression sees finitely many depths,
so it lies in a finite group algebra and cannot witness failure of direct
finiteness.  A viable correction must mix the packet tower with unit-group
elements whose generated subgroup is not already known directly finite; the
recursive idempotents alone cannot do it.
