# A fixed eight-cell normal form for finite Thompson-wreath targets

2026-09-08. Code-free group and prefix calculations. This is an exact
equivalence and an explicit finite system, not a construction of a
solution. No hyperlinearity assumption on Thompson's group `V` is used.

## 1. The packet and the precise equivalence

Use the shorter words from the
[eight-word certificate](leavitt-eight-word-exact-reduction-2026-09-08.md).
Put `E=F_2^3`, with basis `e_1,e_2,e_3`, and

```text
P=C_3*E,       Q=P/<<T_8>>,
T_8={r,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8}.
```

The shared words, with `[X,Y]=XYX^(-1)Y^(-1)`, are

```text
gamma(X)=c X c^(-1),       gamma^2(X)=c^(-1)Xc,
d=[b_2,gamma(b_1)],        h=gamma^2(d),
a=[d,h],                  e=gamma(d),
A=a e a^(-1),             D=gamma^2(A),       r=(Ac)^2,
u=[b_2,gamma(b_3)],        w=[gamma^2(b_1),a],
p_0=gamma(b_2),           q_0=w,
p_1=[e,u],                q_1=[gamma^2(b_3),b_1],
X_0=p_0 q_0 p_0,          X_1=p_1 q_1 p_1,    B=X_0 X_1.
```

Setting `c=1` makes every row of `T_8` trivial: the commuting `b_i`
give `d=h=a=e=A=D=u=w=p_1=q_1=1`, while `X_0=b_2^2=1`.
Thus the projection onto `E` descends and its marked section survives.
Writing `N` for its kernel gives

```text
Q=N semidirect E,       N=<<c>>_Q.
```

For `x in E`, write `b_x=product_i b_i^(x_i)` and
`c_x=b_x c b_x^(-1)`. Moving the `b_i` in any word to the right shows
that the eight `c_x` generate `N`. These assertions require no result
about its perfectness or its embedded Thompson subgroups.

The following four statements are equivalent:

1. A homomorphism `psi:N->V` satisfies `psi(c)!=1`.
2. A homomorphism `Q->V^X semidirect F`, with `X,F` finite and `F`
   acting by coordinate permutations, retains `c`.
3. A homomorphism `Q->V` retains `c`.
4. The eight-tail system in Section 3 has a solution in `V` with
   `z_0!=1`.

Moreover, in statement 3 the images of all three `b_i` may be fixed
in advance to flip the corresponding digit of the first three binary
digits. The image of `c` then preserves those eight prefix cells.
In particular this normalized map is injective on the marked `E`.
The normalized homomorphism is newly constructed and need not be
conjugate to the original witness.

This removes the finite wreath target and the unknown commuting
involutions from the existence question. It does not produce the eight
remaining tail maps.

## 2. Left actions and the eight-cell embedding

Let `Omega={0,1}^N`, and use ordinary left actions: in `XY`, the map
`Y` acts first. For `x in E`, let `p_x` be its three-digit binary word.
On tuples `f=(f_x) in V^E`, set `(y.f)_x=f_(x+y)`. Then

```text
(f,y)(g,z)=(f (y.g),y+z),
Pi(f,y)(p_x alpha)=p_(x+y) f_(x+y)(alpha).             (1)
```

Formula (1) is a homomorphism into `V`. On an input in cell `x`, the
composite first applies `g_(x+z)` and then `f_(x+z+y)`, exactly the
displayed product. Each component has a finite prefix table, so their
finite union after adjoining the prefixes `p_x` is again a prefix
table. If the action is trivial, its prefix permutation forces `y=0`
and each tail forces `f_x=1`; hence `Pi` is injective.

For eight chosen tail maps `z_x`, define

```text
C(p_x alpha)=p_x z_x(alpha),
F_i(p_x alpha)=p_(x+e_i) alpha.                        (2)
```

Thus the `F_i` are three fixed commuting involutions, generating the
regular permutation action of `E` on the prefix cells. The condition
`C^3=1` is exactly `z_x^3=1` for every `x`. This means order dividing
three, not that every tail must be nonidentity.

When evaluating a word with total `E` coordinate zero, its tail on
cell `x` can also be read by a word-rewriting rule: scan left to
right, start a cursor at `x`, move the cursor by `e_i` at a letter
`b_i`, and append `z_cursor` or its inverse at `c` or `c^(-1)`.
The emitted word is the coordinate value. This is a rewriting of the
group product, not the order in which letters act on a point; point
actions remain right to left.

## 3. The complete shared-coordinate system

All subscripts below lie in `E`, and additions are modulo two. For each
`x`, form the following words in the eight unknowns `z_y`:

```text
d_x = z_(x+e_2) z_(x+e_1+e_2)^(-1) z_(x+e_1) z_x^(-1),
h_x = z_x^(-1) d_x z_x,
a_x = [d_x,h_x],
e_x = z_x d_x z_x^(-1),
A_x = a_x e_x a_x^(-1),
D_x = z_x^(-1) A_x z_x,

u_x = z_(x+e_2) z_(x+e_2+e_3)^(-1) z_(x+e_3) z_x^(-1),
k_x = z_x^(-1) z_(x+e_1),
w_x = k_x a_(x+e_1) k_x^(-1) a_x^(-1),
m_x = z_x z_(x+e_2)^(-1),

P_(1,x) = [e_x,u_x],
Q_(1,x) = z_x^(-1) z_(x+e_3)
          z_(x+e_1+e_3)^(-1) z_(x+e_1),
X_(0,x) = m_x w_(x+e_2) m_x^(-1),
X_(1,x) = P_(1,x) Q_(1,x) P_(1,x),
B_x = X_(0,x) X_(1,x).                               (3)
```

The repeated last `P_(1,x)` in `X_(1,x)` is intentional. The source
word is `p_1 q_1 p_1`, and no involution relation on `p_1` is being
silently added. In contrast, `p_0` is a conjugate of `b_2` and really
is an involution.

Require, for every `x`,

```text
z_x^3=1,       d_x^2=1,       (A_x z_x)^2=1.           (4)
```

For each fixed `x`, substitute `A=A_x, B=B_x, D=D_x` in the following
six further equations, using the distinct convention `X^Y=Y^(-1)XY`:

```text
B^3=1,
(AB)^4=1,
D^(-1) A^(B D A D A A^(B A))
       A^(B^(-1) D A D A A^(B^(-1) A))=1,
[A^(B^(-1) D A D),
 A^(B^(-1) D A D A^B A^(B^(-1) A))]=1,
[A^(B D A D),
 A^(B^(-1) D A D A^B A^(B^(-1) A))]=1,
[A^(B D A^(B D A)),
 A^(B D A D A^B A^(B^(-1) A))]=1.                    (5)
```

Equations (4)--(5) are eight order-three equations and 64 coordinate
equations from the packet, on eight variables in `V`. Adjoin `z_0!=1`.
There is no unspecified decoder, choice of commuting involutions,
coefficient-ring realization, or identification of Thompson copies in
this system.

### Authentication of the mixed coordinates

The cursor rule applied to
`d=b_2 c b_1 c^(-1) b_2 c b_1 c^(-1)` emits the first row of (3).
The same calculation with `b_1` replaced by `b_3` gives `u_x`.
Conjugations by `C` then give `h_x,e_x,D_x`, while the remaining
base-group commutators are evaluated coordinatewise.

For the terms that change prefix cells, the semidirect coordinates are

```text
gamma^2(b_i)=(n_i,e_i),   (n_i)_x=z_x^(-1)z_(x+e_i),
p_0=(m,e_2),            m_x=z_x z_(x+e_2)^(-1).
```

Because these elements are involutions,
`(n_i)_(x+e_i)=(n_i)_x^(-1)` and `m_(x+e_2)=m_x^(-1)`.
Consequently `[gamma^2(b_1),a]` has coordinate
`(n_1)_x a_(x+e_1) (n_1)_x^(-1) a_x^(-1)`, which is `w_x`.
Also `p_0 q_0 p_0` has coordinate `m_x w_(x+e_2)m_x^(-1)`.
Finally `[gamma^2(b_3),b_1]` has coordinate
`(n_3)_x (n_3)_(x+e_1+e_3)`, giving `Q_(1,x)` exactly.
These checks account for every shift and inverse in (3).

## 4. Proof of equivalence

For `1 => 4`, set `z_x=psi(c_x)`. The cursor rewriting is an identity
in the kernel of `P->E`, before imposing the packet. Applied at `x`,
it rewrites `b_x t b_x^(-1)` for each base word `t` as the displayed
word in the `c_y`. Every such conjugate of a packet relation dies in
`Q`. Applying `psi` therefore proves (4)--(5); `z_0=psi(c)!=1`.

For `4 => 3`, use (2). The fixed `F_i` satisfy all the defining
relations of `E`, and (4) gives `C^3=1`. By (3), the coordinate
values of all packet words are precisely (4)--(5), so they vanish.
Thus `c->C, b_i->F_i` descends to `Q->V`. Its first cell detects
`c` because `z_0!=1`. The marked `E` embeds because its action on
the eight prefix cells is regular.

Statement 3 implies statement 2 by taking a single coordinate and
trivial acting group. For `2 => 1`, compose the map in statement 2
with projection to the finite group `F`. The established exact
eight-word certificate forces `c` to die in every finite-dimensional
unitary representation and hence every finite-group representation.
The latter assertion follows by the faithful regular representation
of the finite group. Therefore this projection kills `<<c>>_Q=N`.
The image of `N` lies in `V^X`; since `c` survives, some coordinate
projection restricts to a homomorphism `psi:N->V` retaining it.

This completes the equivalence using only the exact eight-word
certificate and elementary split-extension and prefix calculations.
It does not depend on the separate structural analysis
of the perfect kernel.

## 5. A simple exclusion inside the normalized system

Every solution of (4)--(5) satisfies

```text
d_x=1  =>  z_x=1.                                   (6)
```

Indeed `d_x=1` gives `h_x=a_x=e_x=A_x=1`, and then (4) gives both
`z_x^2=1` and `z_x^3=1`. In particular a family invariant under
translation by `e_1` or by `e_2` is necessarily trivial: in either
case the displayed four-term product for every `d_x` cancels to one.
Thus a successful family must vary in both of these directions.
More locally, the two equalities
`z_x=z_(x+e_1)` and `z_(x+e_2)=z_(x+e_1+e_2)` force `z_x=1`.

These are scoped algebraic obstructions, not an exclusion of all eight
tail maps. No invariance under `e_3`, equality of tail conjugacy classes,
or independent normalization of the tails is assumed: independently
conjugating them would generally change the prescribed bit flips.

## 6. The remaining falsifiable task

A constructive witness consists of eight finite prefix-replacement
tables representing `z_x`, satisfying (4)--(5), with `z_0!=1`.
Products and equality can be checked by finite common prefix
refinement. No table-depth bound or such witness is provided here.

The fixed eight-cell embedding is the elementary finite-wreath
construction available in `V`; novelty is not claimed for that general
construction. Its application here supplies the full shared-coordinate
equations and fixes the original three involutions without losing any
finite-wreath witness.

This does not exclude other hyperlinear targets, equate failure of
this system with nonhyperlinearity, or construct a normalized-HS
approximation. It also does not revisit the separate finite-edge
amalgam obstruction.
