# A specific missing Laurent coherence word and a finite cell countermodel

2026-09-08. The remaining third affine rank-two packet has a concrete
word target. In the full stable-letter group that target is a word
in the kernel of the literal action; after removing an explicitly
known boundary transvection, it is the same target as in the
abstract quotient `Lambda`.

The isolated rank-two mixed cell does not force this word: an
explicit permutation model on 168 points satisfies that selected
cell and violates the word. In fact it realizes both complete
`GL_3` factors and their common positive root; precisely the
identification of their common opposite root fails. It is not a
countermodel to `Lambda`, `Theta`, or `Theta_shift`. The missing
word is not proved trivial or nontrivial in those groups.

Use the presentation in
[the stable-letter artifact](jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md),
the exact core and quotient in
[the finitary-kernel proof](jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md),
and the kernel comparison in
[the Laurent quotient calculation](jacobson-stable-letter-laurent-quotient-and-local-inner-action-2026-09-08.md).
All commutators are `[x,y]=x y x^(-1)y^(-1)`.

## 1. The fully decorated word and its exact boundary factor

In `Gamma=Theta_shift`, write

```text
c_P=x_13,P,              k_P=x_31,P,
r_Q=x_23,Q,              r_P=x_23,P,
q_Q=w_23,Q,              q_P=w_23,P,
b=q_Q q_P,              zeta=r_Q r_P,
u=[h c_P h,k_P],         v=h u h,
d_P=h r_P h,            D=h zeta h.
```

The old mixed relation and its conjugate by `h` are

```text
[u,D]=zeta,
[v,zeta]=D.                                           (1)
```

The specific coherence target is

```text
E=b v b D,
E=1  iff  b(h u h)b=h(r_Q r_P)h.                       (2)
```

For comparison, the word using only the original tail Weyl element
and original tail root is

```text
e_P=q_P v q_P d_P.                                    (3)
```

Define the following element of the authenticated finite group `C_0`:

```text
v_0=[h x_21,Q h,x_12,Q]
   =I+e_(1,1) epsilon_(2,0).                          (4)
```

The matrix in (4) is a coordinate description inside `C_0`, not
an inference of an abstract relation from an unproved faithful
representation. The finite table also says that this is the local
component of `v`. Consequently

```text
v=v_0 v_1,                  v_1 in C_far.               (5)
```

The exact relation between (2) and (3) is

```text
E=e_P v_0^(-1).                                       (6)
```

Here are all the necessary boundary cancellations. Put
`A_0=h r_Q h`; in `C_0` it is the transvection
`I+e_(1,1) epsilon_(3,0)`. The finite group `B=K x delta(G)`
shows that `q_P` centralizes both `v_0` and `A_0`.
The head Weyl element `q_Q` sends `v_0` to `A_0` and
centralizes `v_1`, the latter by `C_0 x C_far`. Hence

```text
b v b=A_0 q_P v_1 q_P,
D=A_0 d_P.
```

The element `q_P v_1 q_P` centralizes `A_0` and `v_0`,
because `v_1` centralizes `C_0` and `q_P` fixes those two
elements by conjugation. Also `[A_0,d_P]=1`, by conjugating
`[r_Q,r_P]=1` with `h`. Finally `[v_0,d_P]=1`: conjugate
by `h` and use the exact finite-table commutation of
`h v_0 h=I+e_(2,0) epsilon_(1,1)` with `r_P` in `B`.
Thus

```text
E=q_P v_1 q_P d_P,
e_P=v_0 E=E v_0,
```

which proves (6).

In the literal bilateral action, the formulas are particularly
transparent:

```text
pi(v)=I+sum_(n>=0) e_(1,n+1) epsilon_(2,n),
pi(d_P)=I+sum_(n>=1) e_(1,n+1) epsilon_(3,n).
```

Conjugating the first formula by `q_P` changes the source
coordinate from `2` to `3` at positive levels, and leaves its
level-zero source alone. Therefore

```text
pi(e_P)=pi(v_0),              pi(E)=I.                  (7)
```

The sums define operators on finite-support vectors. They do not
describe complex unitary representations. Equation (7) places `E`
in `ker(pi)`. By the previously proved kernel facts it follows that

```text
[E,L]=1,                     t E t^(-1)=E.             (8)
```

Equations (6)--(8) do not prove `E=1`. In particular, literal
triviality cannot be promoted to abstract triviality by faithfulness
on `L` without first proving that `E` belongs to `L`.

## 2. The quotient word and its exact S_4 subpacket

In `Lambda`, all head elements are killed. Drop the tail subscripts
and set

```text
c=x_13,P,          k=x_31,P,
r=x_23,P,          q=w_23,P,
u=[h c h,k],       v=h u h,       d=h r h.
```

Its two mixed relators are

```text
(h q)^3=1,                 [u,d]=r.                    (9)
```

The image of (2) is the word

```text
e=(q h u h q)(h r h)=(q v q)d.                         (10)
```

Under `Gamma/L=Lambda x Z`, the image of `E` is `(e,0)`.
Since `E in ker(pi)` and `ker(pi) intersect L={1}`, the two
targets are exactly equivalent:

```text
E=1 in Gamma  iff  e=1 in Lambda.
```

Its Laurent image is the identity. Indeed `v` has image
`x_12(z)`, whereas both `q v q` and `d` have image `x_13(z)`.

The second relation in (9) yields a useful exact finite group:

```text
<h,u,r> ~= S_4.                                        (11)
```

To prove this, `h,u` generate the prescribed `S_3` inside the
second finite `GL_3` factor, and `u,r,d` are involutions.
Since `r=[u,d]=(u d)^2` is involutive, it centralizes `u,d`.
Consequently

```text
[r,u]=[r,d]=1,
u d u=r d,
h r h=d,              h d h=r.
```

The subgroup `<r,d>` is therefore elementary abelian of order at
most four and is normalized by `<h,u>`. Their actions on its two
displayed generators are the natural generators of
`GL_2(F_2)=S_3`. This bounds the group in (11) by
`V_4 semidirect S_3`, of order 24.

Its Laurent image attains order 24. In the scaled three-coordinate
basis `z e_1,e_2,e_3`, the elements `h,u` act as the usual
`GL_2(F_2)` on the first two vectors, while `d,r` independently
add those two vectors to the third. Thus (11) is faithful and exact.
Conjugating the mixed relation by `h` also gives

```text
[v,r]=d,             [v,d]=[r,d]=1.                    (12)
```

The missing equation (10) says that the other Weyl element `q`
sends `v` to this already specified root `d`.

## 3. A fully finite model of the selected cell with e nontrivial

This construction tests exactly the relations

```text
<h,u> ~= S_3,
<q,r> ~= S_3,
(h q)^3=1,
[u,h r h]=r.                                          (13)
```

The construction will also realize both complete finite factors
and the defining word for `u`, while violating the prescribed
identification of their `k` roots. Thus it does not impose the
entire common `GL_2` of `Lambda`.

Let `B=GL_3(F_2)`, a set of 168 elements, and inside this finite
matrix group put

```text
h=w_12,       r=x_23,       q=w_23,
u=x_21,       v=x_12,       d=x_13.
```

Then

```text
A=<h,u,r> ~= S_4,
D_8=<h,r>=<r,d> semidirect <h>,
h r h=d=q v q,
v notin D_8.
```

For the last assertion, every matrix of `D_8` restricts to the
span of `e_1,e_2` as either the identity or `w_12`; the
restriction of `v=x_12` is neither.

For `g in B`, let `L_g` denote left multiplication by `g` on
the set `B`. Define the following involutive permutation of that
same set:

```text
T(x)=x h       if x in D_8,
T(x)=x         if x notin D_8.                          (14)
```

It commutes with every `L_a`, `a in D_8`. Indeed left
multiplication by `D_8` preserves both `D_8` and its complement,
and on `D_8` it commutes with right multiplication by `h`.

Now use the permutations

```text
H=L_h,       R=L_r,       Q=L_q,       U=T L_u T.        (15)
```

Because `T` centralizes `L_h,L_r`, the subgroup
`<H,U,R>` is `T L_A T`, an exact copy of `S_4`. In
particular the last relation in (13) holds. The first rank-one
group in (13) is its exact `S_3`. The second rank-one group
and the braid involving `H,Q` are unchanged subgroups and
relations in the regular action of `B`. Thus every relation in
(13) holds exactly.

Nevertheless the coherence word

```text
E_perm=Q H U H Q H R H
      =L_q T L_v T L_q L_d                             (16)
```

is nonidentity. Apply it to the basis label `q in B`, with
the rightmost permutation acting first. The product `L_q L_d`
sends `q` to `q d q=v`. Since `v notin D_8`, `T` fixes
this label. Next `L_v` sends it to the identity label, the next
`T` sends that label to `h`, and `L_q` sends it to `q h`.
Therefore

```text
E_perm(q)=q h != q.                                    (17)
```

Permutation matrices give the same exact selected-cell model in
`U(168)`. No computation or search is required. This demonstrates
that a proof of `e=1` must use more than the isolated relations
(13).

There is a stronger description of exactly what the model satisfies.
Let `c=x_13=d` and `k=x_31` in the finite group `B`. Use
the first full packet with generators

```text
C=L_c,           K=L_k,           Q=L_q,
```

and the second full packet with generators

```text
C'=T L_c T=L_c,
K'=T L_k T,
H=T L_h T=L_h.
```

Both are exact faithful `GL_3(F_2)` representations, being the
regular representation and its conjugate by `T`. The indicated
generators generate those groups by elementary row operations.
The positive common-root equation `C'=C` holds because
`c=d` belongs to `D_8`. The second packet's defining word gives

```text
[H C' H,K']=T L_([h c h,k]) T=T L_u T=U.
```

Therefore both full finite-factor tables, this word definition, the
positive-root identification, and both mixed relators of `Lambda`
hold exactly in the model.

The opposite-root identification is the equation that fails:
`K'!=K`. At the identity label, `T` first sends `1` to `h`;
left multiplication by `k` sends that to `k h`, which lies outside
`D_8`. The last `T` consequently fixes it, giving

```text
K'(1)=k h != k=K(1).
```

To check `k h notin D_8`, every element of `D_8` preserves
the coordinate plane spanned by `e_1,e_2`, whereas `k h` does
not. This identifies precisely the missing common-factor equation,
and also precisely why (17) does not show that `e` survives in
the actual group `Lambda`.

## 4. Equivalent centralization of an orthogonal translation word

The two complete finite factors of `Lambda` provide an additional
exact reformulation. Put

```text
s=c k c.
```

The common `GL_2(F_2)` table gives `s^2=1` and
`k=s c s`. In the second `GL_3(F_2)` table, the prescribed
Weyl elements are `h=w_12` and `s=w_13`, and its root table
gives

```text
u=[h c h,k]=s(h c h)s.
```

For the involution `H_0=h s h=s h s`, this implies

```text
v=h u h=H_0 c H_0.
```

In the first `GL_3(F_2)` table,

```text
r=[q k q,c]=s(q k q)s.
```

Substituting `k=s c s` gives, for `Q_0=s q s=q s q`,

```text
r=Q_0 c Q_0.
```

All of these identifications are internal calculations in their
respective authenticated finite factors. Set

```text
B_0=h Q_0,
t_0=B_0^(-1)(q H_0)
   =Q_0 h q H_0
   =s q s h q s h s.                                  (18)
```

Then `d=B_0 c B_0^(-1)` and
`q v q=(q H_0)c(q H_0)^(-1)`. Direct multiplication in
(10) gives

```text
B_0^(-1) e B_0=t_0 c t_0^(-1)c=[t_0,c].               (19)
```

Thus the remaining equation has the equivalent form

```text
e=1  iff  [s q s h q s h s,c]=1.                       (20)
```

For geometric interpretation, the established Laurent map sends
`s,q` to the constant swaps `w_13,w_23`, and sends `h` to
its displayed Laurent monomial matrix. Multiplying these matrices
in the order of (18) gives

```text
kappa(t_0)=diag(z^(-1),z^2,z^(-1)).                    (21)
```

Its matching first and third diagonal entries explain the Laurent
centralization of `x_13(1)`. They do not prove the abstract
commutation in (20): that is exactly the word whose status is being
tested.

Some accompanying translation relations do hold abstractly. Set

```text
D_12=h Q_0=h s q s,
D_23=q H_0=q h s h.
```

The two local Weyl braids and the mixed braid give

```text
D_23 D_12=q h s h h s q s=q h q s,
D_12 D_23=h s q s q h s h=h q s h s h=h q h s.
```

The final expressions agree because `h q h=q h q`, so these
two translation words commute. The local braids also give

```text
s D_12 s=D_23^(-1),
s D_23 s=D_12^(-1).
```

Since `t_0=D_12^(-1)D_23`, it follows that

```text
[t_0,s]=1.                                            (22)
```

Thus the exact translation word already centralizes the common
Weyl element `s`. What remains in (20) is its centralization of
the common elementary root `c`; (22) does not supply that equation.

## 5. What adjoining the word would complete

In the quotient of `Lambda` obtained by imposing `e=1`, the two
rank-one subgroups `<h,u>` and `<q,r>` generate a faithful
`GL_3(F_2)` with the required third-edge root labels. This is a
finite algebraic consequence, with a short verification.

Name its six proposed roots

```text
X_12=v,       X_21=u,
X_23=r,       X_32=q r q,
X_13=d,       X_31=q u q.
```

The added word gives `q v q=d`. The Weyl braid and the
existing identity `u=h v h` then give

```text
q u q=q h v h q
     =q h(q d q)h q
     =(q h q)d(q h q)
     =(h q h)(h r h)(h q h)
     =h(q r q)h.
```

Thus the two involutions `h,q` permute all six labels exactly
as the coordinate swaps `w_12,w_23`. Their group is the
prescribed `S_3` Weyl group. Every elementary-root involutivity
relation holds. Conjugating (12) by this Weyl group gives every
relation `[X_ij,X_jk]=X_ik`. The two commuting pairs in (12)
give the two types of commuting root pairs, with a common row and
with a common column; their Weyl conjugates give all required
commutations in three coordinates. These are the finite-field
Steinberg relations.

The rank-one tables also give `h=u v u` and
`q=r(q r q)r`. Thus the six roots generate the whole subgroup
`<h,u,q,r>`, including the Weyl elements; there is no additional
uncontrolled Weyl factor.

The finite presentation theorem, Steinberg's *Lectures on Chevalley
Groups*, Section 6, Theorem 9 and its following special-linear
example, therefore gives a quotient of `SL_3(F_2)=GL_3(F_2)`;
see the original lecture transcription at
[Generators and relations](https://math.soimeme.org/~arunram/Resources/LOCGS6GeneratorsAndRelations.html).
The Laurent image on the scaled basis `z e_1,e_2,e_3` is the
full finite group, proving faithfulness. Conversely this specified
finite root packet includes `q v q=d`, so it requires the word
`e=1`.

This identifies exactly the finite packet that the word would
complete. It does not prove that the word follows from the present
relations of `Lambda`. Nor does it identify the entire abstract
Laurent cover, prove faithfulness of `pi` on `Gamma`, or establish
the positive operator-norm gap needed for the requested non-MF
conclusion.
