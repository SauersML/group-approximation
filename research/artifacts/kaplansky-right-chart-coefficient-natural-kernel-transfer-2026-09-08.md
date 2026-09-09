# Every right chart coefficient of the literal deletion actor has a kernel

Date: 2026-09-08. Exact algebraic reduction and kernel-transfer
proof. No computation is required for the argument. A separate
bounded MSI probe supplied compatible finite source witnesses;
no rank pass is used in the proof. No Kaplansky counterexample
or group-ring split is constructed.

Use the binary encoding of `K=GL_2(F_4)`, the reduced projectors
`f_0,P_0`, and the complete source identification from
[the two-sector artifact](kaplansky-full-two-sector-relative-transporter-obstruction-2026-09-08.md).
The literal actor is

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
g=diag(a,b).
```

Both blocks are genuine binary Leavitt units. The theorem is

```
For every c in F_2[K],
there is no L with L P_0[g]c f_0=f_0.                (1)
```

The multiplier `L` may have arbitrary ambient group support.
This statement concerns arbitrary right coefficients with the
left projector `P_0` fixed. It does not combine the separate
[left-coefficient theorem](kaplansky-lower-block-and-left-chart-exterior-formulas-2026-09-08.md)
with an arbitrary right coefficient.

## Complete source notation

Let `B_4` be the scalar extension of the free binary boundary
module. The entire exterior source is parametrized by

```
(X,Y) in (B_4 tensor B_4) direct_sum (B_4 tensor B_4),
```

through

```
k_+(xi,eta)=(u_+(xi)+v_+(xi)) wedge u_+(eta)
```

and its conjugate `k_-`. Both forms are fixed by `f_0`. Their
cross-coordinate component proves that either form is nonzero
when its two arguments are nonzero, and the two forms lie in
distinct central-character sectors.

Write the character blocks of `a,b` as `A,B,C,D` in the usual
order. Explicitly,

```
A=omega^2+s_0+t_0,       B=omega+omega^2 s_0+t_0,
C=omega^2+s_1+t_1,       D=omega+omega^2 s_1+t_1.
```

Here `omega^2=omega+1`, and `sigma` conjugates field
coefficients while fixing binary boundary basis vectors. Set

```
Phi_g,+(X,Y)=alt((C tensor A)X+(D^sigma tensor B^sigma)Y),
Phi_g,-(X,Y)=alt((D tensor B)X+(C^sigma tensor A^sigma)Y),

Psi_b,+(X,Y)=alt((C tensor C)X+(D^sigma tensor D^sigma)Y),
Psi_b,-(X,Y)=alt((D tensor D)X+(C^sigma tensor C^sigma)Y).
```

Let `tau` flip the tensor factors in both source coordinates,
and define the source scaling

```
D_z(X,Y)=(zX,z^sigma Y).
```

This scaling is by **input sector**. It is distinct from
scaling the two target coordinates in the left-coefficient
calculation. The map `Psi_b` kills every flip-symmetric source,
including diagonal tensors.

## The right coefficient formula

For a constant right matrix

```
n=[[p,q],[r,s]] in GL_2(F_4),
```

put

```
alpha=p(r+s),       beta=r(p+q),       gamma=r(r+s).
```

The complete source map for `P_0[g][n]f_0` is

```
Phi_g D_alpha+Phi_g D_beta tau+Psi_b D_gamma.         (2)
```

To verify the plus-source calculation, `n` sends the two
field-coordinate vectors `(1,1)` and `(1,0)` to
`(p+q,r+s)` and `(p,r)`. After `g`, the plus-character
contribution projected by `P_0` is therefore

```
p(r+s) alt(C tensor A)
  +r(p+q) alt(A tensor C)
  +r(r+s) alt(C tensor C).
```

The second term is `alt(C tensor A) tau`. The minus target
uses the same three scalars for this input sector. The other
input sector uses their conjugates, giving exactly (2).

For an arbitrary sum `c` in `F_2[K]`, sum the three scalars
over its group elements. Formula (2) still holds. In particular

```
delta=alpha+beta
```

is the corresponding sum of determinants. Although each group
element has nonzero determinant, this sum can vanish.

## Exact reduction to four normalized maps

If `delta=0`, then `alpha=beta`. Every flip-symmetric source is
killed by (2): the two `Phi_g` terms cancel and `Psi_b` kills
the remaining term. A diagonal tensor in either sector gives
an explicit nonzero source kernel.

Suppose `delta!=0`. Set

```
N=I+tau,
H=I+D_(beta/delta) N.
```

In characteristic two, `N^2=0`; source scalings commute with
`N`. Hence `H^2=I`, so `H` is invertible. Also
`Psi_b D_z N=0` for every scalar `z`.
Precomposing (2) by the invertible source map
`H D_(delta^-1)` gives

```
R_gamma/delta=Phi_g+Psi_b D_(gamma/delta).            (3)
```

Thus every right coefficient reduces to one of four maps

```
R_z=Phi_g+Psi_b D_z,       z in F_4,
```

or has the automatic kernel from `delta=0`. A nonzero kernel
of the normalized map transfers back by `H D_(delta^-1)`.

## An auxiliary linear map realizes each normalized test

Let `m_z` denote multiplication by `z` on a binary
field-coordinate pair, and put

```
a_z=a+b m_z.
```

The character blocks of `a_z` are `A+zC` and `B+zD` on the
plus input, with their conjugates on the minus input.
Consequently (3) is exactly the exterior source map obtained
from the linear block operator

```
diag(a_z,b).
```

This is an equality of linear representation maps. No claim
is made that `a_z` or this auxiliary block operator is a
Leavitt unit or an ambient group element. Its noninjectivity
will instead provide the kernel of the genuine group-ring
operator in (2).

## Transfer of a natural kernel to the exterior source

**Lemma.** Let `a'` be any binary-linear operator on the first
field-coordinate pair, and let `b'` be invertible. If `a'`
has a nonzero natural kernel vector, then
`P_0 Lambda^2(diag(a',b')) f_0` has a nonzero source kernel.

Extend scalars and write a nonzero natural kernel vector as

```
q=u_+(x)+u_-(y),
a' u_+(x)=a' u_-(y).
```

If a nonzero input component is itself killed, the conclusion
is immediate: for example, if `x!=0` and `a'u_+(x)=0`, then
`k_+(xi,x)` is a nonzero killed source for any nonzero `xi`.
The minus case is identical. This covers a missing input
component and also the case where both images vanish.

Otherwise `x,y` are both nonzero, and their common image is
some nonzero vector `v`. Write

```
(b')^-1 v=u_+(xi)+u_-(zeta).
```

At least one of `xi,zeta` is nonzero. The source

```
w=k_+(xi,x)+k_-(zeta,y)
```

is nonzero: the two summands belong to distinct central
sectors, and at least one has both arguments nonzero.
It is fixed by `f_0`.

Let `j` copy the first field-coordinate pair into the second.
After applying `diag(a',b')`, discard the first-field wedges,
which `P_0` kills. The remaining terms combine to

```
j(b'(u_+(xi)+u_-(zeta))) wedge v=j(v) wedge v.
```

This diagonal cross wedge is also killed by `P_0`: its pure
character projections are `J_+(v_+,v_+)` and
`J_-(v_-,v_-)`, both zero, while the mixed characters are
annihilated. This proves the lemma, including its degenerate
cases. All vectors are finite elements of the free module.

## Three literal natural kernels

The field multipliers in the binary basis are

```
m_1=[[1,0],[0,1]],
m_omega=[[0,1],[1,1]],
m_(omega^2)=[[1,1],[1,0]].
```

For `z=1`,

```
a_1=[[0,s_0+s_1],[t_0+t_1,0]].
```

For every nonzero tail vector `eta`, the vector
`((s_0+s_1)eta,0)` is nonzero and is killed by `a_1`, since

```
(t_0+t_1)(s_0+s_1)=1+1=0.
```

The two prefix ranges are disjoint, so
`(s_0+s_1)eta!=0`.

For `z=omega`,

```
a_omega=[[1+s_1,1+s_0+s_1],[t_0,t_1]].
```

Set `h=1^infinity`. Then `(h,0)` is a nonzero kernel vector,
using `s_1h=h` and `t_0h=0`.

For `z=omega^2`,

```
a_(omega^2)=[[s_1,1+s_0],[t_0+t_1,t_1]].
```

Set `u=0^infinity`. Then `(0,u)` is a nonzero kernel vector,
using `s_0u=u` and `t_1u=0`.

The lemma supplies a nonzero exterior source kernel for all
three corresponding normalized maps. For `z=0`, the normalized
map is `Phi_g`, with the previously proved
[period-two kernel](kaplansky-deletion-shear-period-two-exterior-kernel-2026-09-08.md).
All four cases are therefore covered.

For reference, two concise normalized source witnesses
obtained from the lemma are

```
z=omega:
  h=1^infinity, p=0h,
  X=(h+omega p) tensor h,
  Y=(h+omega^2 p) tensor h;

z=omega^2:
  u=0^infinity, w=1u,
  X=omega^2 w tensor u,
  Y=omega w tensor u.
```

Both pairs are fixed by binary Frobenius conjugation. Their
meaning is the input-sector-weighted formula (3), not the
target-weighted left pencil.

## Group-ring consequence and scope

The four normalized kernels and the `delta=0` case give a
nonzero source kernel for `P_0[g]c f_0` for every `c` in
`F_2[K]`. Each scalar-extended source already contradicts an
identity over the binary group algebra. Equivalently, writing
it as `w_0+omega w_1` gives binary source kernels; at least
one of `w_0,w_1` is nonzero because the operators are defined
over `F_2`.

All group-ring coefficients lie in `F_2[H]`, where
`H=〈K,g〉`. Conditional expectation onto this subgroup algebra
preserves a proposed identity in (1), so the obstruction also
applies to an arbitrary ambient left multiplier `L`.

The result covers arbitrary right chart coefficients for the
literal deletion pair, with `P_0` fixed on the left. It does
not cover an independently chosen coefficient on both sides
of `[g]`, arbitrary coefficients outside `F_2[K]`, every
incomparable prefix pair, or every transporter. It does not
prove a common kernel for all right coefficients. No finite
rank pass or relative-character spectral classification is
needed for the theorem.

The later [simultaneous-choice calculation](kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md)
gives two explicit left-and-right choices with injective auxiliary
natural maps. Thus the natural-kernel mechanism does not extend
to them directly. Their complete exterior maps remain to be
decided.
