# Natural-head linear gauges and the TS augmentation obstruction

2026-09-08. These are exact structural restrictions on characteristic-two
linear models of the strengthened Jacobson presentation. They permit
nonmonomial matrices. They do not exclude arbitrary marked amenable or
MF quotients, and do not establish a complex operator-norm gap.

Use a field `k` of characteristic two and based vector spaces `M,Y`,
with `M!=0`, in the natural-head module

```text
V=(k^3 tensor M) direct-sum Y,
V_i=e_i tensor M.
```

The head `G_Q=GL_3(F_2)` acts naturally on the first tensor factor
and trivially on `Y`. The tail `G_P` commutes with it. Write
`K=GL(<e_1,e_3>)_Q`, and let `H` be an arbitrary linear involution
centralizing `K`. No monomial assumption is made in Section 1.

The head root differences `E_ij=x_ij,Q-I` and their products
`E_ij E_ji` show that the tail preserves every `V_i` and `Y`, with
the same multiplicity operator on the three `V_i`. Likewise, the
two overlap roots show that `H` preserves `V_1`, `V_3`, and
`V_2 direct-sum Y`, with the same operator on `V_1,V_3`.
These facts hold without semisimplicity or finite dimensionality.

## 1. Complete linear normal form forced by the first braid

Let the tail swap `w_23,P` act by involutions `T` on `M` and `S`
on `Y`. Write `U=H|_(V_1)=H|_(V_3)`, so `U^2=I`.
In the order `V_3,V_2,Y`, write

```text
H=[U 0 0; 0 a p; 0 q D],
B=pi(w_23,w_23)=[0 T 0; T 0 0; 0 0 S].               (1)
```

Here `p:Y->M` and `q:M->Y`. The first braid is equivalent to
`HBH=BHB`. The upper left block gives `T a T=0`, hence `a=0`.
Set `F=T U T`. Comparing the other blocks, and imposing `H^2=I`,
gives precisely

```text
p q=I_M,        p D=0,        D q=0,
D^2=I_Y+q p,
p S=F p,        S q=q F,
D S D=S D S.                                         (2)
```

There is also the equation on the omitted summand `V_1`:

```text
U T U=T U T.                                         (3)
```

Conversely, `U^2=T^2=S^2=I`, equations (2)--(3), and the matrix
(1) with `a=0` imply both `H^2=I` and the first braid. For example,
the middle diagonal equation of `HBH=BHB` becomes
`p S q=F p q=F`, and its two remaining off-diagonal equations
follow from `pD=Dq=0` and the intertwining equations in (2).
Thus no omitted matrix condition is hidden in the normal form.

The split injection `q` gives

```text
Y=q(M) direct-sum ker(p).                              (4)
```

The tail involution `S` preserves both summands and acts as `F`
on `q(M)` under the identification by `q`. The operator `D`
vanishes on `q(M)`, preserves `ker(p)`, and is an involution on
that kernel. There its braid with `S` is exact. Finally,

```text
H(0,m,0)=(0,0,q m),
H(0,0,q m)=(0,m,0).                                   (5)
```

In particular, the first braid forces the entire second head-coordinate
block to be exchanged with a split linear subspace of `Y`. A general
linear countermodel cannot avoid that exchange by leaving a nonzero
`V_2->V_2` block in `H`. It can change the embedding `q`, which
need not send basis vectors to basis vectors.

For one copy of the natural head over `F_2`, the tail on `M=F_2`
is trivial and `U=1`. Writing `q(1)=p_0` and the map `p` as a
functional `ell`, the equations reduce to

```text
H|_(k e_2 + Y)=[0 ell; p_0 D],
ell(p_0)=1,      S p_0=p_0,      ell S=ell,
D p_0=0,        ell D=0,        D^2=I+p_0 ell,
D S D=S D S.                                         (6)
```

The vector `p_0` may be a nontrivial linear combination of tail
basis vectors. Formula (6) makes that freedom explicit.

## 2. The TS cell rules out augmentation-preserving linear gauges

For a based algebraic vector space, let its augmentation functional
be the sum of the finitely many coefficients of a vector. Denote the
augmentation functionals on `M` and `Y` by `epsilon_M,epsilon_Y`,
and on `V` by their sum over its four displayed summands.

**Proposition.** Suppose every tail matrix and `H` preserve this
augmentation functional. Then the TS word

```text
c=x_13,P,       r=x_23,P,
z_Q=x_23,Q,     z=z_Q r,
k=k_Q k_P=x_31,Q x_31,P,
W=[[H c H,k],H z H] z                                (7)
```

is nonidentity. Neither braid nor the raw commutation `R=1` is
needed for this conclusion.

**Proof.** Put `V_0=V_1 direct-sum V_3`, `L=V_2 direct-sum Y`.
Let `Z:V_0->L` be the head root difference `z_Q-I`; it sends
`V_3` identically to `V_2` and vanishes on `V_1`. Set

```text
J=H_L Z H_0^(-1),
A=H c H,       B_0=H r H,       u=[A,k_P].              (8)
```

All three of `u,B_0,r` are block diagonal for `V_0 direct-sum L`,
and preserve `V_1,V_3` separately. The head part of `k` drops
from the commutator because `A` centralizes `K`. Also
`H z H=(I+J)B_0`.

For a block diagonal `g`, write `g.X=g_L X g_0^(-1)`.
The tail commutes with the head root, so `r.Z=Z`. Thus
`z=(Z,r)` is an involution, and `W=I` is equivalent to its
preceding commutator being `(Z,r)`.
The off-diagonal block calculation

```text
[(0,u),(J,B_0)]=(u.J-[u,B_0].J,[u,B_0])
```

shows that `W=I` would force

```text
[u,B_0]=r,          u.J-r.J=Z.                         (9)
```

Write `lambda=epsilon_L`. Let `chi` be the functional on `V_0`
which is zero on `V_1` and equals `epsilon_M` on `V_3`.
It is nonzero because `M` has a nonempty basis. Block preservation
and the augmentation hypotheses imply

```text
lambda H_L=lambda,        chi H_0=chi,
lambda u_L=lambda,        chi u_0=chi,
lambda r_L=lambda,        chi r_0=chi.
```

Consequently `lambda J=lambda Z H_0^(-1)=chi`, and

```text
lambda(u.J)=chi=lambda(r.J),
lambda Z=chi!=0.
```

Applying `lambda` to (9) gives `0=chi`, a contradiction. QED.

This excludes many nonmonomial gauges: in characteristic two an
invertible matrix can preserve augmentation while having several
nonzero entries in a column. In particular, over `F_2`, all columns
may have arbitrary odd support sizes. Both the tail action and `H`
may have that form; neither has to be a permutation.

If the tail remains a permutation action over `F_2`, a model with
`W=I` therefore requires at least one basis vector whose image under
`H` has even support. An augmentation-preserving finite perturbation
of a permutation involution cannot repair the TS defect. This is an
exact obstruction to that proposed repair, not a norm estimate.

## 3. What remains possible

The new augmentation condition is not forced by overlap centrality or
the first braid. For a small explicit illustration take `M=F_2`,
`Y=F_2 y_1 + F_2 y_2`, and trivial tail. Fix `e_1,e_3,y_2`,
and define

```text
H e_2=y_1+y_2,          H y_1=e_2+y_2.                 (10)
```

This is an involution centralizing `K`. It has the form (6), with
`p_0=y_1+y_2`, `ell(y_1)=1`, `ell(y_2)=0`, and
`D y_1=D y_2=y_2`. Therefore the first braid holds, although
`H` does not preserve augmentation. It is not a model of both
braids: the tail is trivial, so the second braid would force `H=I`.
This example only verifies that the excluded augmentation condition
cannot be inferred from the first-braid normal form.

More generally, the TS off-diagonal equation (9) can admit cancellation
between arbitrary linear combinations. Section 2 identifies one
functional which forbids that cancellation when it is preserved; no
argument here supplies such a functional for every linear model.
Head representations other than sums of the natural module and the
trivial module are outside both sections. These results therefore do
not determine whether the strengthened presentation has a marked
amenable quotient or a mark-preserving norm-matrix-corona image.
