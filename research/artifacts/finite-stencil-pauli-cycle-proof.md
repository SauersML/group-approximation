# Exact cyclic periodization of a finite Pauli stencil

Let

```text
X = [[0,1],[1,0]],
Z = [[1,0],[0,-1]].
```

These matrices are self-adjoint involutions and satisfy `XZ=-ZX`; therefore

```text
[X,Z]=XZXZ=-I_2.
```

For an integer `m>=1`, work on `H_m=(C^2)^(tensor m)`.  Define `p_i` (resp.
`q_i`) to be `X` (resp. `Z`) in tensor factor `i` and the identity elsewhere,
and put `J=-I_(H_m)`.  Operators at distinct tensor sites commute, while
`[p_i,q_i]=J` at every site.  Identifying the scalar centers therefore gives
the standard central product `K_m` of the `m` Pauli groups.

Let `S` be the unitary which cyclically permutes tensor factors so that

```text
S p_i S^(-1)=p_(i+1),
S q_i S^(-1)=q_(i+1).
```

Fix a finite `D subset Z\{0}` and choose `m>max_(r in D)|r|`.  For any
`r in D`, the residue `r mod m` is nonzero: otherwise `m` divides the nonzero
integer `r`, impossible when `|r|<m`.  Consequently

```text
[p_0,S^r p_0 S^(-r)] = [p_0,S^r q_0 S^(-r)] = 1,
[q_0,S^r p_0 S^(-r)] = [q_0,S^r q_0 S^(-r)] = 1.
```

Together with the same-site identities, these are every defining relation of
the finite-stencil presentation.  The assignments

```text
t |-> S, p |-> p_0, q |-> q_0, J |-> -I
```

therefore define an exact representation with finite image
`K_m rtimes <S>`.  In normalized Hilbert--Schmidt norm,

```text
||J-I||_2^2 = tr(((-2I)^*)(-2I)) = 4,
```

so the marked central involution remains at distance `2` from the identity.
