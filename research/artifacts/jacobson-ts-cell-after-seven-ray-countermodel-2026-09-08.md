# The TS cell remains independent after the two braids and first raw commutation

2026-09-08. This note identifies one explicit additional relation which the
amenable seven-ray quotient does not satisfy. It proves independence of
that relation, not positivity of a matrix gap or non-MF existence.

## 1. The finite presentation and the additional word

Use `G=GL_3(F_2)`, `F=G_Q x G_P`, and the presentation

```text
Gamma=<F,h | h^2=1, [h,K]=1, (h b)^3=1, (h d_P)^3=1>,
b=(w_23,w_23),       d_P=(1,w_13),
K=GL(<e_1,e_3>)_Q,   w=(I+E_13)_Q.
```

Define the packet elements

```text
c=(I+E_13)_P,
z_Q=(I+E_23)_Q,       z_P=(I+E_23)_P,
z=z_Q z_P,           k=(I+E_31)_Q (I+E_31)_P.
```

Commutators use `[a,b]=a b a^(-1) b^(-1)`. Put

```text
R=[h c h,z_P],
Gamma_1=Gamma / <<R>>,
W=[[h c h,k],h z h] z,
Gamma_2=Gamma_1 / <<W>>.                              (1)
```

All three groups have explicit finite presentations: the finite packet
can be specified by its multiplication table. The seven-ray construction
gives an amenable quotient of `Gamma_1` retaining the whole packet. The
result here is

```text
W != 1 in Gamma_1.                                    (2)
```

Nevertheless `W=1` in the literal Jacobson elementary group. Thus (1)
adds a genuinely new mixed relation, and the head mark remains nontrivial
in `Gamma_2` by the literal Jacobson representation.

## 2. Compute the word in the seven-ray quotient

Use the explicit improved action in
[the seven-ray countermodel](jacobson-two-braid-seven-ray-countermodel-2026-09-08.md).
Its ray labels are

```text
A_i=e_i,       B_i=sum_(j!=i)e_j,       C=e_1+e_2+e_3.
```

Write `a_(i,n)` and `b_(i,n)` for the corresponding basis vectors of
the seven-ray module. These are independent basis vectors; the formulas
for the *labels* do not impose linear relations between ray basis vectors.
This distinction is essential below.

The head acts naturally on `a_(1,0),a_(2,0),a_(3,0)` and fixes the
remaining basis vectors. The tail acts by the seven-point permutation
representation on every positive level and fixes level zero. The
involution `H` exchanges `a_(2,n)` with `a_(1,n+1)`, fixes the
`A_3` ray and `a_(1,0)`, and exchanges `b_(1,n),b_(2,n)` without
a shift for positive `n`. It fixes all other boundary vectors and the
`C` ray.

Let `E_(v;y)` denote the rank-one operator sending the basis vector `y`
to `v` and every other basis vector to zero. The seven-ray construction
proves

```text
H c H=z_P,          H z_P H=c.                         (3)
```

The second equality follows from the first and `H^2=1`. The head root
`z_Q` sends `a_(3,0)` to `a_(3,0)+a_(2,0)`. Therefore

```text
D:=H z_Q H=I+E_(a_(1,1);a_(3,0)),
H z H=D c.                                            (4)
```

Because the head and tail packet factors commute, the exact finite-group
commutator identity gives

```text
u:=[H c H,k]=[z_P,k_P]=(I+E_21)_P,
[u,c]=z_P.                                            (5)
```

The tail permutation `u` sends the ray label `A_1=e_1` to
`B_3=e_1+e_2`. It fixes the boundary. Consequently

```text
D':=u D u^(-1)=I+E_(b_(3,1);a_(3,0)).                  (6)
```

The operators `D,D'` commute: they have the same source basis vector,
and neither target has an `a_(3,0)` component. They also commute with
`z_P`, since the transvection `I+E_23` fixes both labels `A_1,B_3`
and the tail fixes the boundary. Using the general commutator identity
`[u,Dc]=[u,D] D[u,c]D^(-1)` now yields

```text
[u,Dc]=D'D z_P.
```

Multiplication by `z=z_Q z_P` and cancellation of `z_P^2` gives

```text
W=D'D z_Q
 =I+E_(a_(1,1);a_(3,0))
    +E_(b_(3,1);a_(3,0))
    +E_(a_(2,0);a_(3,0)).                             (7)
```

In particular

```text
W a_(3,0)=a_(3,0)+a_(1,1)+b_(3,1)+a_(2,0).
```

The three added vectors are distinct basis vectors. Thus `W` is a
nonidentity involution in this amenable quotient of `Gamma_1`, proving
(2). The calculation is exact over `F_2`; it is not a claim about a
chosen complex representation of the quotient.

There is also a quantitative exclusion inside this particular quotient.
Let `b_Q=(I+E_12)_Q`. In (7), write the added vector as
`v=a_(1,1)+b_(3,1)+a_(2,0)` and let `f` be the coefficient functional
of `a_(3,0)`. The head element `b_Q` fixes `f` and sends `v` to
`v+a_(1,0)`. The rank-one factors commute, so

```text
[b_Q,W]=I+E_(a_(1,0);a_(3,0))=w       in A_7.          (7a)
```

In particular `w` belongs to the normal closure of `W` in `A_7`.
For every unitary representation `rho` of `A_7`, the triangle inequality
and unitary invariance of the norm give

```text
||rho(w)-I|| <= 2 ||rho(W)-I||.                       (7b)
```

If `rho(w)` is nonidentity, it is an involution and the left side of
(7b) equals two. Hence `||rho(W)-I||>=1`. Thus this entire quotient,
including arbitrary unitary representations of it, cannot retain the
head while making the added TS word arbitrarily close to the identity.
The relation (7a) is proved in `A_7`; it is not asserted in `Gamma_1`.

## 3. The same word is a literal TS relation

In `J=F_2<S,T | TS=1>`, put `P=ST`, `Q=1-P`, and use

```text
h=[[Q,S,0],[T,0,0],[0,0,1]],
c=x_13(P),           z=x_23(1),           k=x_31(1).
```

Direct multiplication and the elementary commutator relations give

```text
h c h=x_23(T),       h z h=x_13(S),
[h c h,k]=x_21(T),
[[h c h,k],h z h]=x_23(TS)=x_23(1)=z.                 (8)
```

Since `z` is an involution, (8) gives `W=1`. Also
`R=[x_23(T),x_23(P)]=1` because the two elements are in the same
root subgroup. The two braid and overlap relations hold in the literal
Jacobson action as already verified in the two-braid reduction. Thus
there is a homomorphism

```text
Gamma_2 -> EL_3(J)
```

retaining the full finite packet. In particular the image of `w=x_13(Q)`
is nonidentity, as it adds the first head basis vector to the third.
There is no assertion that this homomorphism is injective.

## 4. Exact scope of the remaining question

The two braids, the entire finite packet, and the first raw commutation
`R=1` all admit the amenable marked model. Equation (7) proves that
adding `W=1` removes this particular model. Equation (8) proves that
adding it does not remove the literal head witness.

Whether every norm-matrix-corona representation of `Gamma_2` kills the
head is not settled here. Failure of one amenable model supplies no
uniform lower bound on the relator defects. In particular no coordinate
projection, polar decomposition, or common square carrier has been
constructed from these additional relations. This explicit finite
presentation records a testable next relation without treating its
independence as the missing non-MF theorem.
