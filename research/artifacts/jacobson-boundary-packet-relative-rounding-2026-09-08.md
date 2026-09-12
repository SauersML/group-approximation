# Coherent relative rounding of the finite boundary packet

2026-09-08. This proves a dimension-independent correction of the
boundary packet while holding the original finite packet fixed. The
remaining mixed relators are controlled, not made exact. No matrix gap
or non-MF conclusion is asserted.

## 1. Statement and exact common subgroup

Use the finite groups and words of
[the shifted-packet artifact](jacobson-shifted-gl3-and-boundary-gl5-packets-2026-09-08.md):

```text
F=G_Q x G_P,                  G=GL_3(F_2),
K_Q=GL(<e_1,e_3>)_Q,          K_P=GL(<e_1,e_3>)_P,
a_1=x_21,Q,  a_2=x_23,Q,     a_3=a_1 a_2,
A_Q=<a_1,a_2>,               P_Q=A_Q K_Q,
c=x_13,P,   k=x_31,P,        r=x_23,P,
G_*=<c,k,h> ~= GL_3(F_2),
s=h c h=x_23,*,              u=[s,k]=x_21,*,
z_i=a_i r,                   B_i=h z_i h,
W=[u,B_2] z_2,               L_a=[u,h a_2 h] a_2.
```

The coordinate order in `G_*` is the shifted order: `h=w_12`,
`c=x_13`, and `k=x_31`.

Let `pi_F:F->U(d)` and `pi_*:G_*->U(d)` be exact unitary
representations which agree on `K_P=<c,k>`. Assume their images
of `K_Q` and `G_*` commute. All displayed words are formed from
these same matrices. Set

```text
w=||W-I||,       ell=||L_a-I||,
D=10 ell+128 w.                                      (1)
```

Define the finite group

```text
J=Hom(F_2^2,F_2^3) semidirect (K_Q x G_*),
|J|=64*6*168=64512.                                  (2)
```

The target coordinates in `Hom(F_2^2,F_2^3)` are the shifted
coordinates; the two source coordinates are the exterior head
coordinates `e_(1,0),e_(3,0)`. The source and target factors act
by `X |-> g X k_0^(-1)`. The two head generators correspond to
the matrices whose first or second column is `e_2`, respectively.

In the literal Jacobson realization, the exact intersection is

```text
J intersect F = L' := P_Q x K_P.                      (3)
```

For a direct verification, inspect the far shifted blocks. A shifted
matrix that also preserves every original level must belong to `K_P`.
After removing it, an element of the root group in (2) preserves
original levels only when both target columns lie in the shared line
`<e_(2,0)>`. These are exactly `A_Q`. The remaining source factor
is `K_Q`. Conversely these subgroups all lie in both packets. This
proves (3), including its specified embedding in each packet.

The claim is: if `D<=1/100`, there is a unitary representation
`pi'_J:J->U(d)` whose restriction to `L'` is exactly `pi_F` and
whose value `H'=pi'_J(h)` satisfies

```text
||H'-H|| <= 85 D,             H=pi_*(h).              (4)
```

All the new shifted matrices are defined by `pi'_J|G_*`. In
particular `c,k` keep their original values, so they and `H'`
satisfy the entire shifted packet together. The head subgroup
`A_Q K_Q` also keeps its original values. The boundary relation
`[u',H' a_2 H'] a_2=I` then holds exactly, with
`u'=[H' c H',k]`. Thus the construction corrects one common
operator `H`, rather than separate copies of its occurrences.

## 2. Approximate orbit relations from the two word errors

Since `K_Q` commutes with `u,h`, conjugating by it gives

```text
||[u,B_i]-z_i||=w                 (i=1,2,3).           (5)
```

Here `u,B_i,z_i` are involutions. If `C_i=[u,B_i]`, then
`u C_i u=C_i^(-1)`. Comparing with the involution `z_i` in
(5) yields `||[u,z_i]-I||<=2w`. Products of two distinct
`z_i` are the nonidentity elements of `A_Q`; hence

```text
||[u,a_j]-I|| <= 4w.                                 (6)
```

The exact shifted group has the row four-group
`A_*={1,u,s,u s}`. The group `K_P` permutes its three nonidentity
elements and commutes exactly with every `a_j`. Consequently (6)
holds with any element of `A_*` in place of `u`. Every element
of the point stabilizer `P_*=A_* K_P` therefore satisfies

```text
||[p,a_j]-I|| <= 4w                  (p in P_*).       (7)
```

Choose, once and for all, elements `g_v in G_*` with `g_v e_2=v`
for the seven nonzero vectors `v`, taking

```text
g_(e_2)=1,   g_(e_1)=h,   g_(e_1+e_2)=u h.
```

Define actual unitary matrices

```text
A_(j,v)=pi_*(g_v) a_j pi_*(g_v)^(-1),
A_(j,0)=I.                                          (8)
```

They are involutions. The exact identities

```text
A_(3,v)=A_(1,v) A_(2,v),
[A_(1,v),A_(2,v)]=I                                 (9)
```

follow from the head four-group. For every `g in G_*`, the element
`g_(gv)^(-1) g g_v` belongs to `P_*`. Equation (7) thus gives

```text
||pi_*(g) A_(j,v) pi_*(g)^(-1)-A_(j,gv)|| <= 4w.     (10)
```

The boundary word has the same error `ell` for all three choices
of `a_j`, by `K_Q` conjugation. With the selected representatives,
this is

```text
||A_(j,e_1+e_2)-A_(j,e_2) A_(j,e_1)|| <= ell.
```

Conjugate by an element taking the ordered pair `(e_2,e_1)` to
any ordered pair of distinct nonzero vectors `(v,v')`. Three
applications of (10), one for each orbit matrix, give

```text
eta=ell+12w,
||A_(j,v+v')-A_(j,v) A_(j,v')|| <= eta.              (11)
```

If one vector is zero or the two vectors coincide, (11) holds with
zero error. Thus it applies to all vectors.

The exact source identity (9) supplies the cross commutations.
Compare the two products

```text
(A_(1,v) A_(1,v'))(A_(2,v) A_(2,v')),
(A_(1,v) A_(2,v))(A_(1,v') A_(2,v')).
```

Both are close to `A_(3,v+v')`: the first within `2 eta`,
the second within `eta`. Cancel the common leftmost and rightmost
unitaries. The result is

```text
||[A_(1,v'),A_(2,v)]-I|| <= 3 eta.                   (12)
```

## 3. An approximate representation of the whole finite group

Write the root group in (2) as ordered pairs `(v,v')` of target
vectors, and put

```text
f_E(v,v')=A_(1,v) A_(2,v').
```

Using (12) once to interchange the two middle factors, and (11)
once for each source family, gives

```text
||f_E(e) f_E(e')-f_E(e+e')|| <= 5 eta.                (13)
```

The representation `rho` of `H_0=K_Q x G_*` is exact by the
initial commuting-packet assumption. Its covariance with `f_E`
has the following bound:

```text
||rho(t) f_E(e) rho(t)^(-1)-f_E(t.e)||
       <= 5 eta+8w                  (t in H_0).       (14)
```

For the target factor `G_*`, (14) uses (10) on the two source
families, for a bound `8w`. For the source factor `K_Q`, the
conjugate of each `A_(j,v)` is exactly the corresponding one of
the three matrices in (9). After writing the product of these two
images, at most one interchange of a first-source and second-source
factor costs `3 eta`, and at most two additions cost `eta` each.
This gives `5 eta`. Combining the commuting factors proves (14).

Now use the unique semidirect-product normal form to define

```text
f_J(e,t)=f_E(e) rho(t).                               (15)
```

Every value is unitary and `f_J(1)=I`. For a product in `J`, one
application of (14) and one of (13) give the uniform defect

```text
||f_J(x) f_J(y)-f_J(xy)||
       <= 10 eta+8w = 10 ell+128w = D.                (16)
```

The restriction to `L'` is exactly the original representation.
Indeed, in its normal form the two root columns are scalar multiples
of `e_2`, so (8) gives precisely the original head matrices
`a_1,a_2`. Its linear factor lies in `K_Q x K_P`, where the
two given representations agree with `pi_F`. Therefore

```text
f_J(l)=pi_F(l)                     for every l in L'. (17)
```

This exact restriction is the input that allows a relative correction.
It does not assume any unproved simultaneous correction of overlapping
packets.

## 4. A finite-group relative correction lemma

Let `T` be any finite group, let `S` be a subgroup, and let
`f:T->U(d)` satisfy `f(1)=I` and

```text
max_(x,y in T) ||f(x) f(y)-f(xy)|| <= D <= 1/100.
```

Assume `f|S=pi` is an exact representation. There is an exact
representation `sigma:T->U(d)` such that

```text
sigma|S=pi,
max_(g in T) ||sigma(g)-f(g)|| <= 85D.                (18)
```

Here is a dimension-preserving proof. On
`K=ell^2(T) tensor C^d`, let `lambda` be left translation on
the first factor, and define the isometry

```text
V xi=|T|^(-1/2) sum_(g in T) delta_g tensor f(g)^* xi.
```

The defect hypothesis gives

```text
||lambda(h)V-V f(h)|| <= D.
```

Put `P=V V^*` and average its conjugates:

```text
Q=|T|^(-1) sum_(h in T) lambda(h) P lambda(h)^*.
```

Then `Q` commutes with `lambda(T)`, is a positive contraction,
and satisfies `||Q-P||<=2D`. Its spectrum lies in
`[0,2D] union [1-2D,1]`. Let `P'` be its spectral projection
for `[1/2,1]`. It commutes with `lambda(T)` and

```text
||P'-P|| <= ||P'-Q||+||Q-P|| <= 4D = tau < 1.         (19)
```

Projections at distance less than one have the same rank. Thus
`P'` has rank `d`, exactly. The isometry

```text
V'=P' V (V^* P' V)^(-1/2)
```

has range `P'K`. Since `V^*P'V >= (1-tau^2) I`,

```text
||V'-V|| <= tau+(1/sqrt(1-tau^2)-1) <= 2tau <= 8D.
```

The second inequality holds for `tau<=1/2`, as is certainly the
case here. Therefore

```text
rho(g)=V'^* lambda(g) V'
```

is an exact representation on the original dimension `d`, and

```text
||rho(g)-f(g)|| <= 2||V'-V||+D <= 17D.                (20)
```

It remains to hold the subgroup fixed. Average the close
representations on `S`:

```text
T_0=|S|^(-1) sum_(l in S) pi(l) rho(l)^*.
```

Then `pi(l)T_0=T_0 rho(l)` and `||T_0-I||<=17D<1`.
It is invertible. Its unitary polar factor `U` satisfies the same
intertwining identity. Every singular value of `T_0` lies within
`17D` of one, so

```text
||U-I|| <= ||U-T_0||+||T_0-I|| <= 34D.
```

Finally set `sigma(g)=U rho(g) U^*`. Its restriction to `S`
is exactly `pi`, and (20) gives

```text
||sigma(g)-f(g)|| <= 2||U-I||+17D <= 85D.
```

This proves (18). All averaging groups in this argument are finite.
The dimension of the auxiliary space is irrelevant to the constants;
the corrected representation acts on `C^d`.

## 5. The corrected common operator and the remaining mixed cells

Apply (18) to (15), taking `T=J`, `S=L'`, and using (16)--(17).
This proves (4) and the stated exact compatibility with the unchanged
packet `F`. In particular

```text
H'=pi'_J(h),
c=pi'_J(c),       k=pi'_J(k),
s'=H' c H',       u'=[s',k]=pi'_J(u)
```

are one coherent shifted representation. The finite group `J` has
the boundary relation `[u,h a_2 h]=a_2`, so its corrected version
is exact. This conclusion uses the corrected subgroup representation,
not an independent choice of corrected `u,s`, or `h` matrices.

Let `b=(w_23,w_23)` in the unchanged packet, and let

```text
beta=||(H b)^3-I||,       kappa=85D.
```

The first braid contains three occurrences of `H`. The word
`W=[[H c H,k],H z_2 H] z_2` contains twelve occurrences of
`H`, counting those in inverse words. Unitary telescoping gives

```text
||(H' b)^3-I|| <= beta+3 kappa,
||W(H')-I|| <= w+12 kappa.                            (21)
```

The second braid and `H'^2=I` already hold in the corrected
finite shifted packet. Also `[H',K_Q]=I` holds exactly in `J`.
If needed, the redundant raw commutation has the bound

```text
||[H' c H',r]-I|| <= 12 ||W(H')-I||,                 (22)
```

by the shifted-packet calculation in the preceding artifact.

Thus approximate models with `w,ell,beta` tending to zero can be
replaced, on the same dimensions and with the entire original
packet fixed, by models with an exact common boundary packet and
exact boundary cell, while their remaining mixed errors still tend
to zero. The head mark is unchanged. Equation (21) does not make
`W` or the first braid exact and does not prove that either has a
positive gap after the correction.
