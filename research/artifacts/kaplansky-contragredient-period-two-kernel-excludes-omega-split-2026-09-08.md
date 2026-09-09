# A contragredient period-two kernel excludes the omega chart split

Date: 2026-09-08. Exact binary representation obstruction.

The literal candidate `T_omega` has no group-ring left inverse
on its source corner. Its previously proved injectivity in
the ordinary boundary exterior square remains valid. A
different, contragredient representation has the explicit
finite source kernel proved here. Together with the earlier
omega-square obstruction, this excludes all four literal
choices of the two parameters and the two actor orientations.
It does not resolve Kaplansky's direct-finiteness conjecture.

## A genuine group automorphism and the transformed candidate

On the binary Leavitt algebra let `*` be the anti-involution
that fixes scalars and exchanges `s_i,t_i`. On matrices,
include matrix transpose. In the natural free boundary
module it is exactly transpose for the basis pairing.
Every displayed operator and its inverse has finite rows
and columns, so its restricted contragredient action is
well defined on finitely supported vectors.

The map on units

```
theta(q)=(q^-1)^*
```

is an involutive group automorphism, and extends linearly
to a group-ring automorphism. It is not an operation that
reverses a proposed group-ring product.

Write

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b),

ell_z=diag(1,z^-1),
n_z=[[0,z^-1],[1,0]],
T_z^epsilon=P_0[ell_z][g^epsilon][n_z]f_0,
z in {omega,omega^2},       epsilon in {+1,-1}.
```

The natural binary matrices `a,b` are self-adjoint. Hence

```
theta(g)=g^-1,
a^-1=[[1+s_0t_0,s_0],[t_0,1]],
b^-1=[[1+s_1t_1,s_1],[t_1,1]].
```

The constant parent, child, and central order-three
generators defining the projectors are symmetric matrices.
Their images under `theta` are their squares, so their
order-three norm idempotents are fixed. The central block
removed in forming `f_0,P_0` is fixed as well: inverse
transpose preserves the finite special-linear subgroup
and its element orders. Thus, literally in the group ring,

```
theta(f_0)=f_0,       theta(P_0)=P_0.
```

Multiplication by `omega` is the symmetric binary matrix
`[[0,1],[1,1]]`. Direct inversion and transpose give

```
theta(ell_z)=ell_(z^2),       theta(n_z)=n_(z^2).
```

Consequently

```
theta(T_z^epsilon)=T_(z^2)^(-epsilon).             (1)
```

In particular, testing the actual `T_omega^(+1)` in the
restricted contragredient exterior-square representation
is exactly testing `T_(omega^2)^(-1)` in the ordinary
boundary exterior square. The source remains `im f_0`
and the target remains `im P_0`.

## The inverse-actor two-sector map

Let `sigma` conjugate the coefficients of `F_4`, fixing
the binary tails, and put

```
E_0=s_0t_0,       E_1=s_1t_1,       E_0+E_1=I.
```

The character blocks of `a'=a^-1,b'=b^-1` are

```
A'=I+omega^2E_0+s_0+t_0,
B'=omega E_0+omega^2s_0+t_0,
C'=I+omega^2E_1+s_1+t_1,
D'=omega E_1+omega^2s_1+t_1.
```

For `z=omega^2`, define the auxiliary first block
`H'=a'+m_z^-1 b' m_z`, whose character blocks are

```
A_z'=A'+C'=omega^2+s_0+s_1+t_0+t_1,
B_z'=B'+omega D'
    =omega^2+E_0+omega^2s_0+s_1+t_0+omega t_1.
```

The complete two-sector source map is

```
F_+'(X,Y)=alt((C' tensor A_z')X
                 +(D'^sigma tensor B_z'^sigma)Y),
F_-'(X,Y)=alt((D' tensor B_z')X
                 +(C'^sigma tensor A_z'^sigma)Y).
```

By the same invertible normalization used in
[the simultaneous-candidate construction](kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md),

```
E_z T_z^(-1) (tau D_z)=F',       z=omega^2.        (2)
```

## A literal period-two kernel in both sectors

Use distinct actual tails

```
alpha=(01)^infinity,       beta=(10)^infinity,
epsilon=s_1 beta.
```

They satisfy

```
s_0 beta=alpha,       s_1 alpha=beta,
t_0 beta=0,           t_1 beta=alpha,
t_1 alpha=0,
E_0 beta=0,           E_1 beta=beta,
E_0 alpha=alpha,       E_1 alpha=0.
```

Take

```
x=beta+omega^2alpha,       y=alpha+omega^2beta,
X=x tensor beta,          Y=y tensor beta.         (3)
```

For short verification set

```
v=alpha+beta,
t=omega^2beta+epsilon,
t'=omega beta+epsilon.
```

The plus-sector quantities are exactly

```
A_z' beta=t,
B_z'^sigma beta=t+v,
C'x=beta+omega alpha+epsilon,
D'^sigma y=omega^2alpha+epsilon.
```

Thus `C'x+D'^sigma y=v` and
`t+D'^sigma y=omega^2v`. The full plus coordinate is

```
C'x wedge t+D'^sigma y wedge (t+v)
  =v wedge (t+D'^sigma y)
  =v wedge omega^2v=0.
```

The minus-sector quantities are exactly

```
A_z'^sigma beta=t',
B_z' beta=t'+v,
D'x=alpha+omega^2epsilon,
C'^sigma y=omega^2beta+omega alpha+omega^2epsilon.
```

Here `D'x+C'^sigma y=omega^2v` and
`omega^2t'+D'x=v`. Consequently the full minus coordinate is

```
D'x wedge (t'+v)+C'^sigma y wedge t'
  =v wedge (omega^2t'+D'x)
  =v wedge v=0.
```

These identities include the off-core tail `epsilon` and
verify the whole exterior map, not a projected window.

## Binary source for the actual transformed candidate

The source in (3) has `Y=omega^2X^sigma`. Scaling both
tensors by `omega^2` makes the pair Frobenius fixed.
Applying the source change `tau D_z` from (2) then gives
the actual candidate source

```
X_T=beta tensor (alpha+omega beta),
Y_T=beta tensor (alpha+omega^2beta)=X_T^sigma.      (4)
```

Use the standard source vectors

```
u_+=e_1+omega e_2,       v_+=e_3+omega e_4,
u_-=e_1+omega^2e_2,      v_-=e_3+omega^2e_4,
k_±(xi,eta)=(u_±xi+v_±xi) wedge u_±eta.
```

The corresponding vector is

```
w=k_+(beta,alpha+omega beta)
    +k_-(beta,alpha+omega^2beta).
```

It has the following explicit binary form. Write
`a_i=e_i alpha` and `b_i=e_i beta`. Then

```
w=(b_1+b_3) wedge (a_2+b_1+b_2)
    +(b_2+b_4) wedge (a_1+a_2+b_1).               (5)
```

The two occurrences of `b_1 wedge b_2` cancel, leaving
nine distinct basis wedges. In particular (5) is nonzero.
The full source parametrization gives `f_0w=w`, and
(2)--(4) give

```
T_(omega^2)^(-1) w=0.                             (6)
```

If `L T_omega^(+1)=f_0` held anywhere in the ambient
group ring, applying the genuine automorphism `theta`
would give

```
theta(L) T_(omega^2)^(-1)=f_0.
```

Its action on (5) contradicts (6). Thus the original
`T_omega^(+1)` has no such left inverse, independently
of the support allowed for `L`.

## All four literal parameter/orientation choices are excluded

The [earlier period-four certificate](kaplansky-two-sided-omega-square-period-four-kernel-2026-09-08.md)
already excludes `T_(omega^2)^(+1)`. Applying (1) excludes
`T_omega^(-1)` as well. The present period-two certificate
excludes `T_(omega^2)^(-1)` directly and, by (1),
`T_omega^(+1)`. Therefore all four displayed literal
choices `T_z^epsilon` have no group-ring source-corner
left inverse.

This does not exclude arbitrary simultaneous finite-chart
coefficients, sums of corrected actors, or other actors.

## Discovery and compatibility with the positive control

One bounded MSI probe, completed normally in 0.952 seconds
including the wrapper, found the nine-term actual source
on the period-two core and stopped at the first kernel.
The kernel-probe process exited successfully; no probe was
left running. Independently, the inverse-actor periodic
outside equations give `U=alpha tensor beta` and
`V=beta tensor beta`, which yield (3). The proof above is
explicit algebra and does not rely on the finite probe.

The [ordinary exterior-square injectivity theorem](kaplansky-omega-corrected-deletion-full-exterior-injectivity-2026-09-08.md)
for `T_omega^(+1)` remains correct. It tests one group
representation; (5) is a kernel in its contragredient
representation. No surjectivity claim or source/target
interchange is used to pass between them. This gives an
exact example where passing the complete ordinary boundary
exterior-square test is insufficient for a group-ring split.
