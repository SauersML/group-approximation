# One nonnormal packet against the concrete Leavitt lift defect

Let `R=L_F2(1,2)`, `G=R^x`, `S=F_2[G]`, and use the order-three corner
`e=[g]+[g^2]`.  This note audits the smallest literal construction before
writing a correction equation.

## A bare Hecke letter cannot lift `s_0`

For a group unit `y`,

```text
pi_e(e(1+[y])e)=1+y.
```

Thus equality with `s_0` forces `y=1+s_0`.  This element is not a unit.  The
Leavitt algebra is `Z`-graded with `deg(s_i)=1`, `deg(t_i)=-1`.  If a finite
graded sum `b` satisfied `(1+s_0)b=1`, let `[m,n]` be its degree range.  If
`n>=0`, its degree `n+1` term is the uncancelled `s_0b_n`, nonzero because
`t_0s_0=1` makes left multiplication by `s_0` injective.  If `n<0`, then
`m<0` and the degree `m` term is the uncancelled `b_m`, since multiplication
by `s_0` raises degree.  Both contradict a degree-zero right side.  Hence
`1+s_0` has no right inverse.

Allowing corner units on both edges changes the question exactly to a
two-unit decomposition.  Indeed

```text
p e(1+[y])e q  |->  p q + p y q,
```

the sum of two units; conversely `s_0=a+b` with `a,b` units gives
`s_0=a(1+a^-1b)`.  No two-unit decomposition of `s_0` is established in the
graph.  Therefore the proposed one-letter construction cannot be started
from the available data.

## The concrete ten-term defect

Use the three-unit lifts from the self-similarity chart.  In `M_2(R)` they
are

```text
U1=[[1,0],[t1,1]]             V1=[[1,s1],[0,1]]
U2=[[t0+1,1],[1,0]]          V2=[[s0+1,1],[1,0]]
U3=[[0,1],[1,1]]             V3=U3.
```

Their nine products are

```text
U1V1=[[1,s1],[t1,0]]
U1V2=[[s0+1,1],[t1+1,t1]]
U1V3=[[0,1],[1,t1+1]]
U2V1=[[t0+1,s1+1],[1,s1]]
U2V2=[[t0+s0+1,t0+1],[s0+1,1]]
U2V3=[[1,t0],[0,1]]
U3V1=[[0,1],[1,s1+1]]
U3V2=[[1,0],[s0,1]]
U3V3=[[1,1],[1,0]].
```

The prefix normal form distinguishes these nine matrices from one another
and from the identity.  Hence, for

```text
t~=sum_i[Ui],       s~=sum_j[Vj],
D=t~s~+1,
```

`D` has support exactly ten.  It belongs to `ker(pi)`, since
`pi(t~)pi(s~)=t_0s_0=1`.

Put

```text
A=e t~ e,       B=e s~ e,
Delta=AB+e.
```

Then `Delta in ker(pi_e)` and, without hiding the extra middle-corner term,

```text
Delta = e D e + e t~ z s~ e,       z=1+e.              (1)
```

This is a completely explicit finite defect.

## The single-packet correction equation

Inside the constant `S_3`, let

```text
k=[u]+[v]+[w],       u+v+w=0 in R.
```

Thus `k in ker(pi)`, while `ek=ke=0`.  For any group unit `x`, define the
conjugated packet

```text
P_x=e[x]k[x^-1]e.                                    (2)
```

It always belongs to `ker(pi_e)`; it vanishes for the original packet and
can be nonzero only after leaving its packet normalizer.  Keeping `B` fixed,
the modified lift `A_x=A+P_x` satisfies the desired one-sided relation
exactly when

```text
P_x B = Delta.                                        (3)
```

If (3) holds, then `A_xB=e`, while
`pi_e(BA_x)=s_0t_0!=1`, so it is already the required direct-finiteness
witness.  Equation (3), with (1)--(2), is the finite one-nonnormal-packet
target.  The recursive locally finite idempotents do not occur.

The audit does not exhibit an `x` solving (3).  Moreover `x` cannot be kept
inside any subgroup known to have directly finite `F_2` group algebra:
support localization would then make the one-sided inverse two-sided and
force `t_0` to be a unit.  Thus a successful `x` must genuinely engage the
nonsofic part of the Leavitt unit group; finite packet algebra alone cannot
choose it.
