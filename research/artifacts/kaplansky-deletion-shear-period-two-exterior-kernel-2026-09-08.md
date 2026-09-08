# A period-two exterior kernel for the deletion-containing shear pair

Date: 2026-09-08. Exact four-term binary source certificate.
The kernel was found by a bounded MSI probe that completed in
0.411 seconds. The proof below consists of explicit algebraic
identities and requires no computation. No Kaplansky counterexample
or group-ring split is constructed.

Use the binary root encoding of `K=GL_2(F_4)` and the reduced
projectors `f_0,P_0` from
[the first-field-coordinate artifact](kaplansky-first-field-coordinate-transporter-kernel-2026-09-08.md).
Roots `1,2` encode the first field coordinate and roots `3,4` the
second, in the basis `1,omega`, with `omega^2=omega+1`.

## The actors and their inverses

In the binary Leavitt algebra, define

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b),
Z=P_0[g]f_0.
```

These are genuine units. For either `i=0,1`, the exact inverse is

```
[[1,s_i],[t_i,0]]^-1
  =[[1+s_i t_i,s_i],[t_i,1]].
```

Multiplication in both orders gives identity using `t_i s_i=1`.
Thus `g^-1` is the block diagonal matrix of the two displayed
inverses.

This pair uses both creation and deletion coefficients. Its
coefficient algebra contains all `s_0,s_1,t_0,t_1`, so the
creator-to-zero algebra map used for
[the earlier positive-shear control](kaplansky-complete-exterior-injective-positive-shear-control-2026-09-08.md)
does not extend to it: setting `s_i=0` contradicts `t_i s_i=1`.
This observation concerns that particular algebra specialization,
not every possible finite representation of the generated group.

## The four-term source vector

Let the actual binary tails be

```
zeta=(01)(01)(01)...,
eta =(10)(10)(10)...,
chi =0 zeta.
```

Then `zeta=0 eta` and `eta=1 zeta`; all three displayed tails are
distinct. Put

```
a_i=e_i zeta,       b_i=e_i eta,       c_i=e_i chi,
```

where `e_i` selects binary root coordinate `i`. Define

```
w=(a_1+a_3) wedge b_1+(a_2+a_4) wedge b_2.            (1)
```

This is a four-term vector over `F_2`. In particular its
`a_1 wedge b_1` coefficient is one, so it is nonzero.

For the source condition, recall

```
u_+(xi)=(e_1+omega e_2)xi,
v_+(xi)=(e_3+omega e_4)xi,
u_-(xi)=(e_1+omega^2 e_2)xi,
v_-(xi)=(e_3+omega^2 e_4)xi,
k_+(xi,nu)=(u_+(xi)+v_+(xi)) wedge u_+(nu),
k_-(xi,nu)=(u_-(xi)+v_-(xi)) wedge u_-(nu).
```

Both `k` forms are fixed by `f_0`. Direct expansion gives

```
w=omega^2 k_+(zeta,eta)+omega k_-(zeta,eta).          (2)
```

The two cross coefficients are `omega^3+omega^3=0`, and the
remaining coefficients are `omega^2+omega=1`. Consequently
`f_0w=w!=0`.

## Exact image and target cancellation

The literal prefix and deletion actions give

```
g(a_1+a_3)=a_1+b_2+a_3,       g b_1=b_1,
g(a_2+a_4)=c_1+b_3,           g b_2=a_1.
```

For example `t_0 zeta=eta`, `t_1 zeta=0`,
`t_0 eta=0`, `s_1 zeta=eta`, and `s_0 eta=zeta`.
Substitution in (1) yields

```
g w=a_1 wedge b_1+a_3 wedge b_1+b_2 wedge b_1
    +c_1 wedge a_1+b_3 wedge a_1.                    (3)
```

The projector `P_0` kills every wedge entirely inside the first
field-coordinate space, consisting of binary roots `1,2`. On each
pure character sector this is the identity
`P_0(u_+(xi) wedge u_+(nu))=0` and its Frobenius conjugate;
mixed-character wedges have trivial central character and are
annihilated by the reduced projector. This removes the first,
third, and fourth terms of (3).

For the remaining terms define the symmetric alternating forms

```
J_+(xi,nu)=P_0(v_+(xi) wedge u_+(nu)),
J_-(xi,nu)=P_0(v_-(xi) wedge u_-(nu)).
```

Using `e_1=omega^2 u_+ + omega u_-` in the first field coordinate
and `e_3=omega^2 v_+ + omega v_-` in the second gives

```
P_0(a_3 wedge b_1)
  =omega J_+(zeta,eta)+omega^2 J_-(zeta,eta),

P_0(b_3 wedge a_1)
  =omega J_+(eta,zeta)+omega^2 J_-(eta,zeta).
```

Symmetry of both `J` forms makes their sum zero in characteristic
two. Therefore

```
P_0[g]f_0w=0,       f_0w=w!=0.                       (4)
```

This is an exact source kernel in the genuine boundary exterior
representation, using the two distinct periodic tails without
identifying them or replacing them by a quotient model.

## Consequence and scope

Let `H=〈K,g〉`. The natural boundary action and its exterior square
are representations of `H`. Equation (4) contradicts
`LZ=f_0` in `F_2[H]`. If `L` is allowed in a larger ambient group
algebra, conditional expectation onto `F_2[H]` preserves that
proposed identity and gives the same contradiction.

Thus this explicit deletion-containing pair cannot solve the
projective comparison. The kernel is a certificate for this actor;
passing other finite probe domains supplies no general injectivity
conclusion, and no assertion about every deletion-containing or
fully mixed transporter follows from the displayed calculation.
