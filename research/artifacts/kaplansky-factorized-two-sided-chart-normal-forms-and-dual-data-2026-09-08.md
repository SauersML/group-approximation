# Factorized two-sided chart normal forms and their independent dual data

Date: 2026-09-08. Exact finite-chart representation reduction.

For a fixed binary block-diagonal actor `g=diag(a,b)`, every
factorized candidate `P_0 c[g]d f_0`, with `c,d in F_2[K]` and
`K=GL_2(F_4)`, either has an automatic boundary exterior-square
kernel or reduces to one of 256 complete source maps. The ordinary
and contragredient chart arrays require separate data. Their exact
joint ranges, proved below, imply that every ordered pair of the
256 normalized tests is realizable by a single pair `c,d`.

This is a reduction of necessary representation tests. It does not
produce a group-ring left inverse, and it does not cover arbitrary
sums `sum_i c_i[g]d_i`.

## Source, target, and sector conventions

Write `F_4=F_2(omega)`, with `omega^2=omega+1`, and let `sigma`
conjugate coefficients. Let `B_4` be the scalar extension of the
free binary-boundary module. The full `f_0` source is parametrized
by two tensors `(X,Y) in (B_4 tensor B_4)^2`, using

```
k_+(xi,eta)=(u_+(xi)+v_+(xi)) wedge u_+(eta)
```

and its conjugate. The two target sectors are copies of
`Lambda^2 B_4`. With the established character blocks `A,B` for
`a` and `C,D` for `b`, define

```
Phi_+(X,Y)=alt((C tensor A)X+(D^sigma tensor B^sigma)Y),
Phi_-(X,Y)=alt((D tensor B)X+(C^sigma tensor A^sigma)Y),

Psi_a,+(X,Y)=alt((A tensor A)X+(B^sigma tensor B^sigma)Y),
Psi_a,-(X,Y)=alt((B tensor B)X+(A^sigma tensor A^sigma)Y),

Psi_b,+(X,Y)=alt((C tensor C)X+(D^sigma tensor D^sigma)Y),
Psi_b,-(X,Y)=alt((D tensor D)X+(C^sigma tensor C^sigma)Y).
```

Here `alt(x tensor y)=x wedge y`, and `tau` flips both source
tensors. Its fixed space includes diagonal tensors in characteristic
two. Both `Psi_a` and `Psi_b` kill every individually flip-symmetric
source. Define source and target scalings separately:

```
D_z(X,Y)=(zX,z^sigma Y),
E_z(F_+,F_-)=(zF_+,z^sigma F_-).
```

The projector's same-character bilinear coefficient matrix is
`R_0=[[0,1],[1,1]]`: first-field wedges project to zero, while
mixed-field and second-field wedges project to the same exterior
tail form. Mixed-character wedges project to zero.

## Exact formula for arbitrary factorized coefficients

Sums below run over the support of the binary group-ring coefficient.
Put

```
R(c)=sum_m m^transpose R_0 m=[[r_0,r_1],[r_1,r_2]].
```

For `n=[[p,q],[r,s]]`, define

```
M(n)=[[p(p+q),p(r+s)],[r(p+q),r(r+s)]],
M(d)=sum_n M(n)=[[m_0,m_1],[m_2,m_3]].
```

Then the complete exterior map of `P_0 c[g]d f_0` is

```
F_(c,d)=E_r0 Psi_a D_m0
       +E_r1 Phi D_m1+E_r1 Phi D_m2 tau
       +E_r2 Psi_b D_m3.                              (1)
```

For the right-hand orientation, `n` sends the two field-coordinate
vectors in the source to `(p+q,r+s)` and `(p,r)`. The coefficients
of the first-first, second-first, first-second, and second-second
wedges are respectively `m_0,m_1,m_2,m_3`. Since exterior tail
forms are symmetric in characteristic two, the first-second term
is `Phi tau`. On the left, congruence by each constant matrix
gives `m^transpose R_0 m`. Summing independently over `c,d` yields
(1). The output scalings `E` and input scalings `D` occupy their
displayed positions; they are not interchanged.

Let `delta=m_1+m_2`. If `r_1=0` or `delta=0`, every individually
flip-symmetric source is killed. A nonzero diagonal tensor in each
of the two conjugate sectors gives a nonzero binary source kernel.

Otherwise put

```
N=I+tau,
H=I+D_(m_2/delta) N.
```

Since `N^2=0` and source scalings commute with `N`, `H^2=I`.
The cross-source coefficient equals `D_delta H`. Also
`Psi_a D_x N=Psi_b D_x N=0` for every scalar `x`. Consequently

```
E_(r_1^-1) F_(c,d) H D_(delta^-1)
   =Phi+E_u Psi_a D_v+E_z Psi_b D_t,                 (2)

u=r_0/r_1, z=r_2/r_1, v=m_0/delta, t=m_3/delta.
```

All four parameters lie in `F_4`. Every change in (2) is invertible
and preserves binary descent. A nonzero normalized kernel therefore
excludes a group-ring identity `L P_0 c[g]d f_0=f_0`.

## The contragredient arrays are not determined by the ordinary arrays

On constant field matrices, the restricted contragredient
automorphism is `theta(n)=(n^-1)^transpose`. If
`Delta=ps+qr`, then `Delta^3=1` and

```
theta(n)=Delta^-1 [[s,r],[q,p]],

R(n)=[[r^2,Delta+rs],[Delta+rs,s^2]],
R(theta(n))=[[Delta q^2,Delta^2+Delta pq],
             [Delta^2+Delta pq,Delta p^2]],

M(theta(n))=Delta [[s(s+r),s(q+p)],
                   [q(s+r),q(q+p)]].                (3)
```

For example, `I` and `[[1,1],[0,1]]` have the same `R=R_0`,
but their transformed `R` arrays are respectively `R_0` and `I`.
Thus ordinary left data do not determine contragredient left data.

For joint ranges it is convenient to conjugate the second array:

```
R'=R(theta(c))^sigma,       M'=M(theta(d))^sigma.
```

This is only a coordinate convention. The actual contragredient
formula uses `R'^sigma,M'^sigma` in (1), and uses the transformed
actor. For the deletion actor, that actor is `g^-1`.

## Exact realizable joint ranges

The following are equalities of ranges, with `c,d` arbitrary in
`F_2[K]`:

```
{(R(c),R(theta(c))^sigma)}
     =Sym_2(F_4) direct_sum Sym_2(F_4),              (4)

{(M(d),M(theta(d))^sigma)}
     ={(M,M'): M_12+M_21=M'_12+M'_21}.              (5)
```

Thus the paired left arrays have 12 independent binary coordinates;
the paired right arrays have 14. These are minimal linear coordinate
counts for the arrays themselves. In particular `M` also fails to
determine its transformed array. The sole right compatibility is
the conjugated determinant sum in (5).

Here is an elementary span proof, without enumeration. Multiplying
a group element by a central scalar `lambda I` multiplies its
ordinary array by `lambda^2` and its transformed array by `lambda`.
After conjugating the latter, both scale by `lambda^2`. Each joint
range is therefore an `F_4`-linear space. It suffices to test linear
relations on `SL_2(F_4)`, where `ps+qr=1`.

For (4), the six coordinate functions are

```
r^2, 1+rs, s^2, q, 1+p^2 q^2, p.
```

Suppose a linear relation has coefficients `a,b,c,d,e,f` in this
order. Set `r=0`, take any nonzero `s`, put `p=s^-1`, and vary `q`
over all four field elements. The coefficients of `q,q^2` force
`d=e=0`. The constant terms, for all three nonzero `s`, then give
`b=0,f=c`, since `s^-1=s^2`. Finally set `r=1,s=0,q=1` and vary
`p`; this forces `a=c=0`. There is no relation, proving (4).

For (5), the off-diagonal sums in each array are 1 on `SL_2`.
Use seven coordinates

```
m_0,m_1,m_3,m'_0,m'_1,m'_3,delta.
```

On `r=0,p=s^-1=s^2`, these are

```
s+s^2 q, 1, 0, s, s^2 q^2+1, q+s q^2, 1.
```

Let a relation have coefficients `a,b,c,d,e,f,h`. Varying `q`
and nonzero `s` gives, successively, `a=f=0`, `e=0`, and
`d=0,h=b`. The remaining relation is
`b(m_1+delta)+c m_3=b m_2+c m_3=0`. Setting
`r=1,s=0,q=1` and varying `p` gives `b=c=0`. This proves
independence of all seven coordinates and hence (5). The use of
polynomial coefficients is valid because the displayed polynomials
in `q` have degree at most two and vanish at all four field elements.

## Consequence for simultaneous ordinary and contragredient tests

Every ordered pair of normalized parameter tuples in `F_4^4`
is realizable. To see this, prescribe the two left arrays with
off-diagonal entries 1 and with any desired diagonal entries.
Equation (4) realizes them, after conjugating the desired second
array. For both right arrays prescribe off-diagonal entries
`m_1=1,m_2=0`; their determinant sums are both 1. Their four
diagonal entries can be arbitrary by (5). In this construction
the two normalizing shears are both the identity.

Therefore there are exactly 256 realizable normalized parameter
tuples in each orientation, and all `256^2` ordered pairs occur.
The ordinary and contragredient necessary tests can both be applied,
but their normalized parameters have no additional realizability
coupling. This statement neither says that a tuple passes either
test nor identifies distinct tuples with distinct operators.

For the current deletion actor, an exact kernel in either test
excludes the factorized candidate. Finite rank probes can discover
such kernels but cannot prove injectivity on the whole boundary
module. This artifact contains only algebraic derivations and uses
no computational rank results.

## Related proofs

- [Left coefficient formulas](kaplansky-lower-block-and-left-chart-exterior-formulas-2026-09-08.md).
- [Right coefficient normalization](kaplansky-right-chart-coefficient-natural-kernel-transfer-2026-09-08.md).
- [Restricted contragredient and the exact period-two obstruction](kaplansky-contragredient-period-two-kernel-excludes-omega-split-2026-09-08.md).
