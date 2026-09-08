# Splitting the TS cell and reconstructing the first-level root packet

2026-09-08. In the presentation with the exact finite boundary packet,
the TS cell and first braid force a new finite subgroup containing the
entire original packet. This is an abstract group consequence, not a
rank ledger or a restriction to defining representations. It does not
establish a matrix gap or a non-MF group.

## 1. Presentation and notation

Use the finite packets from
[the boundary reconstruction](jacobson-shifted-gl3-and-boundary-gl5-packets-2026-09-08.md)
and [coherent rounding](jacobson-boundary-packet-relative-rounding-2026-09-08.md):

```text
F=G_Q x G_P,                         G=GL_3(F_2),
J=Hom(F_2^2,F_2^3) semidirect (K_Q x G_*),
L'=P_Q x K_P,
Xi=< F *_(L') J | (h b)^3=1, W=1 >.
```

Here `K_Q,K_P` act in coordinates `1,3` of their copies of `G`,
`P_Q` is the head row-two parabolic, and

```text
a_1=x_21,Q,     a_2=x_23,Q,     a_3=a_1 a_2,
c=x_13,P,      k=x_31,P,       r=x_23,P,
h=w_12,* in G_*,
s=h c h=x_23,*,                u=[s,k]=x_21,*,
D_i=h a_i h,                   C=h r h,
z_i=a_i r,                     B_i=D_i C=h z_i h,
W=[u,B_2] z_2,
b=q_Q q_P,      q_Q=w_23,Q,    q_P=w_23,P.
```

The finite group `J` supplies the exact identities

```text
[u,D_i]=a_i,
D_3=D_1 D_2,
[D_i,D_j]=1.                                         (1)
```

The original packet and conjugation by `h` give
`[D_i,C]=1`. The head group `K_Q` commutes with `u,h,r` and
permutes the three `a_i`, so the single relation `W=1` gives
all three equations

```text
[u,D_i C]=a_i r.                                     (2)
```

## 2. The TS cell splits into a tail relation and cross commutations

The commutator identity

```text
[u,D_i C]=[u,D_i] D_i [u,C] D_i^(-1)
```

and (1)--(2) imply

```text
[u,C]=D_i r D_i                 for i=1,2,3.          (3)
```

The equality for `i=1,3`, together with `D_3=D_1D_2`, yields

```text
D_1 r D_1=D_1 D_2 r D_2 D_1,
```

so `r=D_2 r D_2`. Similarly `r=D_1 r D_1`; their product
then gives the same assertion for `D_3`. Substitution into (3)
proves

```text
[r,D_i]=1                  for every i,
[u,h r h]=r.                                        (4)
```

Conjugating the first part by `h` shows `[C,a_i]=1`. Since
`C` already commutes with `K_Q`, it centralizes the full head
parabolic `P_Q`. The elements `u,C,r` are involutions and
`[u,C]=r`; therefore their dihedral relation also gives
`[r,u]=[r,C]=1`.

There is a quantitative version requiring only exact `F,J`. Put
`w=||W-I||`. The three conjugate TS errors all have norm `w`.
The same calculation gives

```text
||[u,C]-D_i r D_i|| <= w.
```

Comparing any two of these equations and using the product relation
among the `D_i` gives

```text
||[r,D_i]-I|| <= 2w,
||[u,C]-r|| <= 3w.                                   (5)
```

Thus (4) follows uniformly as the original TS defect tends to zero.

Conversely, with the finite packets exact, the pure tail relation in
(4) and the single commutation `[r,D_1]=1` imply `W=1`:
conjugation by `K_Q` supplies the other two commutations, and (1)
then reconstructs (2). This gives an equivalent splitting of the
mixed cell; neither part alone is asserted sufficient.

## 3. The first braid supplies a second stabilizer direction

Set `a=a_1`, `D=D_1`, and `d=b a b=x_31,Q`. The element
`d` lies in `K_Q`, so it commutes with `h`. The braid between
the involutions `b,h` is `b h b=h b h`. Consequently

```text
b D b
  =(b h b)(b a b)(b h b)
  =(h b h) d (h b h)
  =h b (h d h) b h
  =h (b d b) h
  =h a h=D.                                          (6)
```

Combine (6) with `[D,r]=1` from (4). Since
`b r b=x_32,P`, the operator `D` centralizes both `x_23,P`
and `x_32,P`, hence `q_P=x_23,P x_32,P x_23,P=w_23,P`. As
`b=q_Q q_P`, it also centralizes `q_Q`.

The exact boundary packet has `[D,c]=1`. Conjugating by `b`
and using (6) gives `[D,b c b]=1`, where `b c b=x_12,P`.
We have proved that `D` centralizes all four tail generators

```text
x_12,P, x_13,P, x_23,P, x_32,P.                      (7)
```

These generate the full stabilizer of the vector `e_1` in `G_P`.
Indeed, a matrix fixing `e_1` consists of an arbitrary invertible
block in coordinates `2,3`, with arbitrary entries in positions
`1,2` and `1,3`.

On the head side, the finite boundary packet already says that `D`
commutes with `x_21,Q`, `x_31,Q`, and `x_23,Q`. The newly proved
commutation with `q_Q` adds the conjugate `x_32,Q`. Thus `D`
centralizes

```text
x_21,Q, x_31,Q, x_23,Q, x_32,Q.                      (8)
```

These generate the full stabilizer of the covector `e_1^*` under
the action `f |-> f g^(-1)` of `G_Q`: equivalently, its matrices
have first row `(1,0,0)`.

For approximate first braid defect `beta=||(h b)^3-I||`, the two
braid replacements in (6) give `||[b,D]-I||<=2 beta`. Together
with (5), this for example gives
`||[b r b,D]-I||<=2w+4 beta`. The subgroup reconstruction below
is stated for exact relations; no unproved rounding of this larger
packet is assumed.

## 4. The full source--target matrix group

The commuting factors `G_Q,G_P` act on head covectors and tail
vectors, respectively. By (7)--(8), for nonzero
`v in F_2^3` and nonzero `f in (F_2^3)^*` the conjugate

```text
D(v,f)=(g_Q g_P) D (g_Q g_P)^(-1),
g_P e_1=v,        e_1^* g_Q^(-1)=f,                  (9)
```

is well-defined. Set it equal to the identity if either argument is
zero. Every value is an involution, and the action of `F` on (9)
is exactly the action on its two arguments.

The finite boundary packet contains the target addition relation
on the `e_1,e_3` plane, for the fixed source `e_1^*`:

```text
D(e_1+e_3,e_1^*)=D(e_1,e_1^*) D(e_3,e_1^*).
```

This is its original natural root-module addition, transported by
the common subgroup `K_P`. Since `G_P` is transitive on ordered
pairs of distinct nonzero vectors, and `G_Q` is transitive on
nonzero covectors, this relation propagates to

```text
D(v+v',f)=D(v,f) D(v',f).                             (10)
```

The source addition relation for `e_1^*,e_3^*` is already
`D_3=D_1D_2` in `J`. The analogous transitivity argument gives

```text
D(v,f+f')=D(v,f) D(v,f').                             (11)
```

The repeated or zero cases of (10)--(11) hold because all values
are involutions and the zero-argument values are the identity.

These two addition laws also force all cross commutations.
Expand `D(v+v',f+f')` first using (10) and then (11), and then
in the reverse order. The resulting equality is

```text
D(v,f) D(v,f') D(v',f) D(v',f')
  =D(v,f) D(v',f) D(v,f') D(v',f').
```

Cancel the first and last factors. This proves
`[D(v,f'),D(v',f)]=1`, including arbitrary choices of the
two rank-one matrices. Therefore the nine coordinate generators
form a quotient of the additive matrix group

```text
N=Mat_(3 x 3)(F_2)_add.                              (12)
```

The literal Jacobson image proves that no quotient has occurred.
In that image, `D(v,f)` adds the level-one vector `v` to the
level-zero component specified by the covector `f`. In block
notation it is

```text
I + (v f)_(level 1; level 0).
```

The product of any two such off-diagonal blocks is zero. The nine
coordinate blocks are independent, so they give all `512` distinct
elements of (12). They are normalized by `F`, with action

```text
X |-> g_P X g_Q^(-1).
```

Their intersection with `F` is trivial: an element of `F` preserves
the original levels, whereas a nontrivial element of `N` has a
nonzero level-zero to level-one block. We have consequently proved
that `Xi` contains the finite subgroup

```text
N semidirect F
  ~= Mat_(3 x 3)(F_2)_add
       semidirect (GL_3(F_2)_Q x GL_3(F_2)_P),

|N semidirect F|=512*168^2=14,450,688.                 (13)
```

This group contains the entire original packet `F`. Its root
generator `D_1` is the same word `h a_1 h` throughout the proof.
Thus (13) is a coherent new mixed consequence, not an independently
chosen representation of another finite group.

## 5. What this does and does not settle

The TS cell now separates into the pure tail relation and the
cross commutations in (4). Together with the first braid, these
relations reconstruct a full natural matrix root group joining
the original head level to the first positive level. This excludes
the possibility of treating that interface as an arbitrary
permutation action on its nonzero labels.

The newly reconstructed packet does not contain `h` as a specified
finite-packet element. No simultaneous correction of this larger
packet and `J` has been proved here. Nor has an opposite root
relation, a finite-dimensional collapse, or a positive operator-norm
gap been deduced from (13). Those require further mixed coherence
arguments.
