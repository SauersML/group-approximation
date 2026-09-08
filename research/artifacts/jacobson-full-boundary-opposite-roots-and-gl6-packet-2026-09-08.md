# Opposite boundary roots and a full six-coordinate finite packet

2026-09-08. This proof concerns the stronger presentation `Theta`, which
imposes the full boundary packet `C=GL_5(F_2) x GL_3(F_2)`. That extra
packet is essential to the argument given here. No assertion that it
follows from `Xi` is made. The conclusion is a new finite subgroup,
not a positive matrix gap or a non-MF conclusion.

All commutators are `[a,b]=a b a^(-1) b^(-1)`. All vector spaces and
coordinate matrices in this note are over `F_2`; they specify abstract
finite-group relations, not restrictions on complex representation types.

## 1. Inputs and the one missing commutation supplied by the full packet

Use the finite packets and embeddings from
[the full boundary construction](jacobson-shifted-gl3-and-boundary-gl5-packets-2026-09-08.md):

```text
F=G_Q x G_P,                      G=GL_3(F_2),
C=GL_5(F_2) x GL_3(F_2),
L=G_Q x K_P,
Theta=< F *_L C | (h b)^3=1, W=1 >.
```

The literal five-coordinate factor acts on the head coordinates
`e_(1,0),e_(2,0),e_(3,0)` and the two tail coordinates
`e_(1,1),e_(3,1)`. Its direct-factor subgroup will be denoted `C_0`.
The other factor is detected on the farther shifted blocks. Put

```text
c=x_13,P, k=x_31,P, r=x_23,P,
s=h c h, u=[s,k], C_r=h r h,
q_Q=w_23,Q, q_P=w_23,P, b=q_Q q_P,
A=x_12,Q, Y=h A h.
```

The full `C` contains the smaller packet `J` used in
[the first-level reconstruction](jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md).
Therefore that proof applies in `Theta` and gives

```text
[u,C_r]=r,                                         (1)
N={D(v,f)} ~= Mat_(3 x 3)(F_2)_add,
D(v,f)=I+(v f)_(level 1; level 0),                  (2)
g_Q g_P D(v,f) (g_Q g_P)^(-1)
   =D(g_P v, f g_Q^(-1)).                          (3)
```

The displayed matrix in (2) describes the faithful literal image;
the covariance and two addition laws for `D` hold abstractly.

Inside `C`, the element `Y` is the transvection from `e_(1,1)`
to `e_(1,0)`. Consequently it centralizes `k=x_31,P`:
the boundary component of `k` adds `e_(3,1)` to `e_(1,1)`,
and its farther component is disjoint from `Y`. Also, exact `F`
and conjugation by `h` give

```text
[Y,k]=1,       [Y,s]=1,       [Y,C_r]=1.              (4)
```

The first identity uses the additional full boundary packet. The
other two use `[A,c]=[A,r]=1` in `F`. Since `u=[s,k]`, (4)
implies `[Y,u]=1`; then (1) implies

```text
[Y,r]=1.                                          (5)
```

Thus, for the smaller presentation `Xi`, this argument reduces the
missing tail stabilizer to the single relation `[h x_12,Q h,k]=1`.
Here that relation is available directly in `C`.

## 2. Both stabilizers of the opposite root

The first braid is the involution braid `b h b=h b h`.
Since `b A b=x_13,Q` belongs to `K_Q` and hence commutes with `h`,
the same two-braid substitution as in the first-level proof gives

```text
b Y b=Y.                                          (6)
```

Inside `C`, `Y` centralizes the full head point stabilizer of `e_1`.
In particular it centralizes `q_Q`. Combining this with (6) gives
`[Y,q_P]=1`. Together with (4)--(5), conjugation by `q_P` now gives
centralization of all four tail roots

```text
x_31,P, x_21,P, x_23,P, x_32,P.                    (7)
```

They generate the full stabilizer of the tail covector `e_1^*`:
its matrices have first row `(1,0,0)`. The corresponding head
stabilizer consists of matrices fixing the vector `e_1`.

For nonzero head vector `x` and nonzero tail covector `phi`, define

```text
Y(x,phi)=(g_Q g_P) Y (g_Q g_P)^(-1),
g_Q e_1=x,       e_1^* g_P^(-1)=phi.                (8)
```

The stabilizers just proved make (8) independent of both choices.
Set `Y(0,phi)=Y(x,0)=1`. Its covariance under `F` is

```text
Y(x,phi) |-> Y(g_Q x, phi g_P^(-1)).                (9)
```

The packet `C_0` supplies addition of head target vectors and addition
of the two tail source covectors `e_1^*,e_3^*`. Transitivity of
`G_Q,G_P` on ordered pairs of distinct nonzero vectors or covectors
transports these to

```text
Y(x+x',phi)=Y(x,phi) Y(x',phi),
Y(x,phi+phi')=Y(x,phi) Y(x,phi').                   (10)
```

The zero and repeated-argument cases follow from involutivity.
Expanding `Y(x+x',phi+phi')` in the two possible orders and
cancelling the first and last factors shows that arbitrary values
of `Y` commute. The faithful literal images

```text
I+(x phi)_(level 0; level 1)
```

make the nine coordinate values independent. Thus they give a second
finite root group

```text
N^op ~= Mat_(3 x 3)(F_2)_add.                       (11)
```

## 3. Every opposite-pair configuration is already visible in C_0

Consider `D(v,f)` and `Y(x,phi)` with all four arguments nonzero.
The orbit of this pair under `F` is determined by the two bits

```text
lambda=f(x),        mu=phi(v).                     (12)
```

For a nonzero vector and covector in dimension three, the general
linear group is transitive on pairs with either fixed value of their
pairing. To see this directly, choose the vector as the first basis
element. For pairing one, choose the other basis elements in the
covector's kernel; for pairing zero, choose the second basis element
outside that kernel and the third inside it.

Accordingly, each class in (12) has a representative with both its
tail vector and tail covector supported on coordinates `1,3`.
The whole head is already in `C_0`. Hence every two-root calculation
for these pairs follows by transporting an exact calculation in `C_0`.
In particular,

```text
lambda=mu=0:       [D(v,f),Y(x,phi)]=1;
lambda=0, mu=1:    [D(v,f),Y(x,phi)]=I+(x f)_Q;
lambda=1, mu=0:    [D(v,f),Y(x,phi)]=t(v,phi).       (13)
```

The second line is a head transvection since `f(x)=0`. In the
third line, define `t(v,phi)` by the commutator with any `x,f`
satisfying `f(x)=1`; necessarily `phi(v)=0`.

This definition is independent of that head choice. A representative
in `C_0` is a transvection supported entirely on the two tail
coordinates, so it centralizes the entire `G_Q`. Conjugating it by
`G_P` preserves this head centralization. Finally, `G_Q` is transitive
on the pairs `x,f` with `f(x)=1`. This proves independence.
It also proves that each `t(v,phi)` is an involution, centralizes
`G_Q`, and satisfies exact tail covariance

```text
g_P t(v,phi) g_P^(-1)=t(g_P v,phi g_P^(-1)).        (14)
```

The remaining class `lambda=mu=1` is the ordinary opposite-root
`GL_2(F_2)` calculation, also transported from `C_0`. In particular
`(D(v,f)Y(x,phi))^3=1`. We do not need this last identity for the
Steinberg commutator presentation below.

## 4. The local tail transvections act naturally on both root groups

For `phi(v)=0`, write `T=I+v phi`, an involution of the tail vector
space. We claim the following exact abstract identities:

```text
t(v,phi) D(w,f) t(v,phi)=D(T w,f),
t(v,phi) Y(x,psi) t(v,phi)=Y(x,psi T).              (15)
```

Here zero arguments mean the identity. It suffices to consider
nonzero arguments.

For the first line, if `phi(w)=1`, the vectors `v,w` are independent
and their span admits a complement in `ker(phi)`. All relevant tail
data can therefore be moved into coordinates `1,3`, where (15) is
an identity of `C_0`. If `w=v`, the same conclusion follows by
choosing any second vector on which `phi` is one.

The only remaining case is that `v,w` are independent and
`phi(w)=0`. Choose a nonzero head vector `x_0` in `ker(f)`, and
choose `f_0` with `f_0(x_0)=1`. The independence in Section 3 gives

```text
t(v,phi)=[D(v,f_0),Y(x_0,phi)].
```

The tested `D(w,f)` commutes with the first factor because `N` is
abelian. It commutes with the second by the first line of (13),
since `f(x_0)=phi(w)=0`. It therefore commutes with their
commutator. This is exactly the first line of (15) in this case.

For the second line, if `psi(v)=1`, choose a second tail vector `z`
with `phi(z)=1, psi(z)=0`, and choose the remaining basis vector
in `ker(phi) intersect ker(psi)`. Again all data fit inside `C_0`.
If `psi=phi`, they also fit in such a two-coordinate packet.

The remaining case has `psi(v)=0` and independent `psi,phi`.
Choose a nonzero head covector `f_0` annihilating `x`, and choose
`x_0` with `f_0(x_0)=1`. In the same commutator expression for
`t(v,phi)`, the tested `Y(x,psi)` commutes with the second factor
because `N^op` is abelian. It commutes with the first by (13),
since `f_0(x)=psi(v)=0`. This proves the second line of (15).

These auxiliary choices handle precisely the configurations that
cannot themselves be placed in a two-dimensional tail plane.

## 5. Tail addition and the full six-coordinate Steinberg relations

Set `t(v,0)=t(0,phi)=1`. When `v,w` are in `ker(phi)`, fix
`x,f` with `f(x)=1` and expand

```text
t(v+w,phi)=[D(v,f) D(w,f),Y(x,phi)].
```

The first line of (15) says that `t(w,phi)` commutes with
`D(v,f)`. The commutator product identity therefore gives
`t(v+w,phi)=t(w,phi)t(v,phi)`. As all three are involutions,
the last two commute. Dually the second line of (15) gives

```text
t(v+w,phi)=t(v,phi)t(w,phi)       if phi(v)=phi(w)=0,
t(v,phi+psi)=t(v,phi)t(v,psi)     if phi(v)=psi(v)=0. (16)
```

Conjugating the defining commutator of another local tail root by
`t(v,phi)` and applying both lines of (15) yields

```text
t(v,phi) t(w,psi) t(v,phi)
   =t(w+phi(w)v, psi+psi(v)phi),                    (17)
```

whenever `phi(v)=psi(w)=0`. The transformed vector and covector
still pair to zero because `T^2=I`.

Let `t_ij=t(e_i,e_j^*)` for distinct tail indices. Equations
(16)--(17) imply

```text
[t_ij,t_jk]=t_ik                  for distinct i,j,k,
[t_ij,t_kl]=1                    if j!=k and i!=l. (18)
```

Now label six coordinates by the three head and three first-tail
coordinates. Define every elementary root `X_ab`, `a!=b`, using
the head transvections when both indices are head, `t_ij` when
both are tail, and the coordinate values of `D,Y` in the two mixed
cases. Then

```text
X_ab^2=1,
[X_ab,X_bc]=X_ac                  for distinct a,b,c,
[X_ab,X_cd]=1                    if b!=c and a!=d. (19)
```

Every case of (19) has already been proved: roots within the head
use its finite table; roots within the tail use (18); head roots
acting on mixed roots use `F` covariance; tail roots acting on mixed
roots use (15); two mixed roots in one direction commute by (2) or
(11); and two mixed roots in opposite directions use (13).

The elementary Steinberg presentation over a finite field identifies
the group with generators (19) as `SL_6(F_2)=GL_6(F_2)`.
The precise imported result is Steinberg, *Lectures on Chevalley
Groups*, Section 6, Theorem 9 and its following special-linear
example; a transcription of the original lecture notes is available
at [Generators and relations](https://math.soimeme.org/~arunram/Resources/LOCGS6GeneratorsAndRelations.html).
Over `F_2`, root additivity is exactly involutivity, so (19) is the
stated presentation. This imports a finite-group presentation theorem,
not a representation-rigidity estimate.

Thus the subgroup `K` generated by these roots is a quotient of
`GL_6(F_2)`. In the faithful literal Jacobson image, these roots are
all elementary matrices on the six displayed coordinates, and they
generate the full `GL_6(F_2)`. The quotient map therefore has trivial
kernel. We have proved

```text
K ~= GL_6(F_2).                                    (20)
```

## 6. Separating the farther original tail

Let `tau:G_P -> K` be the copy acting naturally on the three first-tail
coordinates and fixing the head, now available in (20). Conjugation by
the original `g_P` agrees on every generator of `K` with conjugation
by `tau(g)`: this follows from (3), (9), (14), and head centralization.
Therefore

```text
delta(g)=tau(g)^(-1) g_P
```

centralizes `K`. Moreover, the same covariance proves
`delta(g)delta(h)=delta(gh)`. Its literal action is the original
natural tail action on levels at least two, fixing levels zero and
one. Hence `delta` is injective and its image meets `K` trivially.
Consequently

```text
<K,F> ~= GL_6(F_2) x GL_3(F_2),                     (21)
```

with the second factor `delta(G_P)`. This group contains the entire
original packet `F` and both first-interface root groups.

## 7. The shifted generators satisfy both mixed cells

There is a partial recursive consequence, with a precise remaining
boundary relation. In `C_0`, let `h_0` be the pure swap of
`e_(2,0)` and `e_(1,1)`, and put

```text
h_1=h_0 h,
G_Q,new=tau(G_P),       G_P,new=delta(G_P).
```

The element `h_1` is exactly the `w_12` in the second direct factor
of the original `C`; in particular it is involutive and centralizes
all of `C_0`. The elements `delta(c),delta(k)` are also exactly
the `x_13,x_31` in that second factor: their removed local parts
are supported on `e_(1,1),e_(3,1)`. Thus

```text
<delta(c),delta(k),h_1> ~= GL_3(F_2),
[h_1,tau(K_P)]=1.                                  (22)
```

The two new original factors form an exact direct product by (21).
The new first-braid word uses

```text
b_new=tau(q_P)delta(q_P)=q_P.
```

The original `h b` is `(h_0 q_Q)(h_1 q_P)`. The two displayed
factors commute: `h_1` centralizes `C_0`, `q_P` centralizes
`q_Q`, and `h_0` centralizes `q_P`. For the last assertion,
the local `tau(q_P)` swaps only `e_(2,1),e_(3,1)`, disjoint
from `h_0`, and the residual `delta(q_P)` centralizes `K`.
Inside `C_0`, the two transpositions `h_0,q_Q` have a product
of order three. The old first braid consequently gives

```text
1=(h b)^3=(h_0 q_Q)^3(h_1 q_P)^3=(h_1 b_new)^3.     (23)
```

Likewise split `u=u_0 u_1` according to `C=C_0 x C_far`.
The local part `u_0` is the transvection from `e_(1,1)` to
`e_(2,0)`, and

```text
u_1=[h_1 delta(c) h_1,delta(k)].
```

Both `h_0` and `u_0` centralize the original `r`: its local part
`tau(r)` adds `e_(2,1)` to `e_(3,1)`, and its residual part
centralizes `K`. Since `h_1` centralizes `C_0`, it follows that

```text
h r h=h_1 r h_1,
[u_0,h_1 r h_1]=1.
```

The old pure-tail equation (1) therefore becomes

```text
[u_1,h_1 r h_1]=r.                                 (24)
```

For the new presentation, `a_new=tau(r)` and `r_new=delta(r)`,
so `z_new=a_new r_new=r`. Equation (24) is exactly `W_new=1`.
Thus the shifted generators satisfy both mixed cells and all of
the original and shifted three-dimensional finite-packet data.

This does not yet define an endomorphism of `Theta`: its additional
full boundary packet on the new head and new shifted group has not
been proved. Even the new individual boundary linearity relation

```text
[u_1,h_1 tau(r) h_1]=tau(r)
```

is not isolated by (24), which contains the product
`tau(r)delta(r)`. That distinction is the remaining recursive
coherence requirement.

No membership of `h` in the finite group (21), reconstruction at
every higher level, simultaneous operator-norm correction of all
these packets, or positive mixed gap is asserted. Those are further
requirements; the results here alone do not establish the requested
non-MF conclusion.
