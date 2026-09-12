---
rg: 2
id: unbalanced-root-leak-off-spectral-countermodel-proof
kind: route
title: Tensor the Pauli unbalanced-word packet with an incompatible dihedral involution
target: unbalanced-root-leak-does-not-charge-off-spectral-separators
requires:
  - endpoint-matched-amplification-is-matrix-range-neutral
---

Put

```text
Z=[[1,0],[0,-1]],       X=[[0,1],[1,0]],
F=2^(-1/2)(X+Z),        R=ZF,
```

so `F=F*=F^(-1)`, `FZF=X`, `R^8=1`, and
`ZRZ=R^(-1)`.  On `M_2 tensor M_2`, with `Z'` denoting `Z` in the second
factor, set

```text
T=Z tensor I,                    H=F tensor I,
A_12=A_23=I tensor I,
B_21=Z tensor iZ',               B_32=R tensor I,
W_12=I tensor iZ',               W_23=I tensor I.       (RLP1)
```

These are all unitaries.  Since `T` commutes with the four `A` and `W`
matrices, `eta_L=0`.  The two factors in the unbalanced torus word are

```text
D_12=A_12(HB_21H*)A_12W_12*=X tensor I,
D_23=A_23(HB_32H*)A_23W_23*=FZ tensor I.                (RLP2)
```

Because `XFZ=F`, `(RLP2)` gives `D_12D_23=H`; hence `eta_R=0`.  Also

```text
tr_4([T,H])=tr_2(ZFZF)=0,                               (RLP3)
```

so `eta_B=0`.  Finally `T_1=H*TH=X tensor I`, and therefore

```text
T_1B_21T_1*-B_21=-2B_21,
||T_1B_21T_1*-B_21||_2=2.                               (RLP4)
```

This proves `(RLC1)` with the largest possible unitary commutator defect.

Now let

```text
K=<r,q | r^2=q^8=1, rqr=q^(-1)>
```

be the dihedral group of order sixteen.  The assignments
`v(r)=Z`, `v(q)=R` define a two-dimensional representation.  In the second
factor take

```text
Y_r=iZ',       Y_q=I,       b_r=iZ',       b_q=0.       (RLP5)
```

For every ucp map `Phi:C*(K)->M_2`, the matrix `Phi(u_r)` is self-adjoint.
The trace of a product of two self-adjoint matrices is real, and hence

```text
Re tr_2(b_r* Phi(u_r))=Re[-i tr_2(Z'Phi(u_r))]=0.       (RLP6)
```

Thus the support function at `b` is zero, whereas

```text
Re tr_2(b_r*Y_r)=1.                                    (RLP7)
```

The matched-amplification identity applied to `v` says that the tuple

```text
X~=(v(r) tensor Y_r, v(q) tensor Y_q)=(B_21,B_32),
C=(v(r) tensor b_r, v(q) tensor b_q)=(B_21,0)           (RLP8)
```

has the same separation gap one in `M_4`.  It also has
`sum_s||C_s||_2^2=1` and coordinate operator norm at most one.

The tuple `C` commutes with `T`.  Since

```text
W*(T)=span{I,Z} tensor I,
E_(W*(T))(B_21)=Z tensor tr_2(iZ')I=0,                  (RLP9)
```

it is fully off-spectral.  Equations `(RLP4)` and `(RLP8)` show moreover
that its only nonzero coordinate is exactly the maximally leaking one.
This proves `(RLC2)` and the claim.

The scope restriction is visible in `(RLP5)`:
`Y_r^2=-I`, so the amplified coordinate does not approximately satisfy the
dihedral involution relation.  The example therefore separates the local
energy data from complete positivity without asserting an arithmetic HNN
microstate.
