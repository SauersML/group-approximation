# The eight-word quotient: a perfect kernel and a finite-amalgam obstruction

2026-09-08. Pure group arguments, an explicit finite-field assignment, and
a Bass--Serre tree argument. No computation or Lean verification was run.
These results do not decide hyperlinearity of `H=L_(F_2)(1,2)^x`.

The precise conclusions are

```text
Q = N semidirect C_2^3,
N = < eight conjugate embedded copies of V >,
N = [Q,Q] = the finite-dimensional unitary radical of Q,

Q hyperlinear <=> N hyperlinear => V hyperlinear.       (0)
```

Here `Q` is the specific eight-word quotient, not the full Leavitt unit
group. The reverse implication from hyperlinearity of `V` is not proved.
Section 6 excludes one natural attempt to obtain it by adjoining `V` to
the finite-field core along its `S_3` subgroup.

## 1. Definition of the quotient and its compiled Thompson subgroup

Let

```text
E_3=<b_1,b_2,b_3 | b_i^2=1, [b_i,b_j]=1> = C_2^3,
P=<c | c^3=1> * E_3,
gamma(X)=c X c^(-1),
[X,Y]=X Y X^(-1) Y^(-1).
```

The finite words used here are

```text
d=[b_2,gamma(b_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
A=a e a^(-1),            D=gamma^2(A),
r=(A c)^2,

u=[b_2,gamma(b_3)],       w=[gamma^2(b_1),a],
p_0=gamma(b_2),          q_0=w,
p_1=[e,u],               q_1=[gamma^2(b_3),b_1],
X_0=p_0 q_0 p_0,        X_1=p_1 q_1 p_1,
B=X_0 X_1.                                             (1)
```

Let `rho_1,...,rho_8` be the fixed Bleak--Quick presentation words in
`A,B,D`, in the order and with the explicit substitutions written in
Section 3 of the
[native compiler](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md).
In particular

```text
rho_1=A^2,
rho_4=D^(A D) A^(-1),       X^Y=Y^(-1) X Y.
```

Equivalently, the presentation being used is the presentation of `V` in
[Bleak--Quick, Theorem 2.1, equation (2.3)](https://arxiv.org/html/1511.02123#S2),
with the three generators represented by the right-acting prefix maps

```text
A=(00 01),       B=(01 10)(01 11),       D=(1 00).       (2)
```

Define

```text
T_8={r,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8},
Q=P / <<T_8>>.                                         (3)
```

For clarity, the two omitted presentation relations really do follow in
`Q`. First, `A=a c d c^(-1) a^(-1)` is conjugate to `d`, so `d^2=1`
implies `A^2=1`. Next `(A c)^2=1` gives `A c A=c^(-1)`. Consequently

```text
D=c^(-1) A c=A c^(-1),
D A=c,
A D=c^(-1).                                           (4)
```

Using these equations,

```text
D^(A D)=c D c^(-1)=A.
```

Thus all eight Thompson presentation relations hold, and they define a
homomorphism

```text
iota: V -> Q.                                         (5)
```

Equation (4) already proves `c` belongs to its image. A presentation alone
would not prove injectivity of (5); that requires the following native map.

## 2. Native authentication proves that the Thompson map is injective

Put `R=L_(F_2)(1,2)`. Its generators satisfy

```text
t_i s_j=delta_ij,       s_0 t_0+s_1 t_1=1.
```

Set `s=s_0`, `t=t_0`, and `v=s_0 t_1+s_1 t_0`. In particular `ts=1`,
`vs=s_1`, and `tv=t_1`. With `x_ij(z)=I+z E_ij`, the assignment

```text
q(c)=(123),
q(b_1)=x_12(s), q(b_2)=x_12(t), q(b_3)=x_12(v)         (6)
```

defines a homomorphism `P -> EL_3(R)`: the three root elements commute
and are involutions in characteristic two.

The rule `[x_ij(y),x_jk(z)]=x_ik(yz)` for three distinct indices and
cyclic conjugation by `q(c)` give

```text
q(d)=x_13(1), q(h)=x_32(1), q(a)=x_12(1),
q(e)=x_21(1), q(A)=(12), q(D)=(31),

q(p_0)=x_23(t_0), q(q_0)=x_32(s_0),
q(p_1)=x_23(t_1), q(q_1)=x_32(s_1).                   (7)
```

Use the complete binary prefix code `C=(00,01,1)`. The map

```text
Phi:M_3(R) -> R,
Phi((z_ij))=sum_(i,j) s_(C_i) z_ij t_(C_j)             (8)
```

is an isomorphism: its inverse has `(i,j)` entry `t_(C_i) z s_(C_j)`.
For incomparable words `alpha,beta`, write
`P_alpha,beta=s_alpha t_beta` and `e_alpha=s_alpha t_alpha`. Direct
expansion proves

```text
(1+P_alpha,beta)(1+P_beta,alpha)(1+P_alpha,beta)
  =1+e_alpha+e_beta+P_alpha,beta+P_beta,alpha.           (9)
```

This swaps the two indicated prefix cylinders. Equations (7)--(9) show
that `Phi q(A), Phi q(B), Phi q(D)` are exactly (2), with the source's
right action represented on the left by its inverse. The order
`B=X_0 X_1` is the written source order: inversion of the action, rather
than reversal of the word, converts the conventions.

For an explicit way to detect nontriviality, let `R` act on the free
`F_2` vector space with basis all infinite binary sequences. The operator
`s_i` prepends `i`; `t_i` removes that first symbol when present and is
zero otherwise. These operators satisfy the defining Leavitt relations.
The units in (9) act as the corresponding prefix permutations. A
nonidentity element of `V` moves some infinite sequence, so its operator
is not the identity.

It follows both that `q` kills (3) and that the composite

```text
V --iota--> Q --q_bar--> EL_3(R) --Phi--> R^x           (10)
```

is injective. Therefore `iota` is injective. This is an authenticated
copy of `V` in `Q`; no lifting or injectivity is inferred solely from a
presentation.

## 3. The split quotient and the eight Thompson copies

Sending `c` to `1` and retaining the three `b_i` defines a homomorphism
`P -> E_3`. At `c=1`, commutativity of the `b_i` gives

```text
d=h=a=e=A=D=u=w=p_1=q_1=1,
p_0=b_2, q_0=1, X_0=b_2^2=1, X_1=B=1.
```

All relations in (3) therefore die. We obtain a surjection

```text
p:Q -> E_3,       p(c)=1,       p(b_i)=b_i.            (11)
```

The original map `E_3 -> P -> Q` is a section of `p`. Thus its image is
still isomorphic to `C_2^3`, and, writing `N=ker p`,

```text
Q=N semidirect E_3.                                   (12)
```

For `x=(x_1,x_2,x_3) in F_2^3`, put

```text
b_x=b_1^(x_1) b_2^(x_2) b_3^(x_3),
c_x=b_x c b_x^(-1),
V_x=b_x iota(V) b_x^(-1).                             (13)
```

The eight `c_x` generate `N`. One can verify this without a presentation
theorem: move every `b_i` in a word to the right by conjugating each
intervening power of `c`; this expresses every element of `Q` as a word
in the `c_x` followed by one `b_y`. An element lies in `N` exactly when
that last `b_y` is `1`.

The computation preceding (11) gives `iota(V)<=N`, hence `V_x<=N`.
Conversely, (4) gives `c_x in V_x`. Therefore

```text
N=<V_x : x in F_2^3>=<<c>>_Q=<<iota(V)>>_Q.           (14)
```

Each `V_x` is embedded by Section 2 and conjugation. There are eight
indexed copies in (14); no assertion that they are pairwise distinct,
disjoint, or freely amalgamated is needed or proved.

The infinite simple nonabelian group `V` is perfect. A group generated
by perfect subgroups is perfect: every generator subgroup belongs to
the commutator subgroup of the generated group. Hence `N=[N,N]`.
Since `Q/N=E_3` is abelian,

```text
N=[Q,Q],       Q_ab=E_3.                              (15)
```

## 4. The finite-dimensional unitary radical is exactly N

Every homomorphism `V -> U(k)` is trivial. Indeed a nontrivial one would
be injective by simplicity; its finitely generated complex linear image
would be residually finite by Malcev's theorem. An infinite simple group
cannot be residually finite. This is the established
[exact representation argument](../thompson-v-has-no-nontrivial-fd-unitary-representation.md).

A finite-dimensional unitary representation of `Q` consequently kills
each `V_x`, and hence all of `N` by (14). Conversely, composing `p` with
the faithful regular unitary representation of `E_3` detects every
element of `Q` outside `N`. Thus

```text
intersection_(k>=1, pi:Q->U(k)) ker pi = N.            (16)
```

The intersection of the kernels of all finite-group homomorphisms is
also `N`: a finite group has a faithful unitary representation, and (11)
already separates all elements outside `N`.

In particular `N` has no nontrivial finite-dimensional unitary
representations. This is an exact representation statement; (16) does
not identify a hyperlinear radical or provide a uniform HS gap.

## 5. What the structure proves about hyperlinearity

Subgroup closure gives `Q hyperlinear => N hyperlinear => V hyperlinear`.
The first implication reverses because `N` has finite index in `Q`.
Here is a direct microstate argument in the split situation (12).

Take canonical-trace microstates `phi` for a finite subset of `N` large
enough to contain all eight `E_3` conjugates needed for a finite test in
`Q`. On eight blocks, set

```text
U(n)=diag_(x in E_3) phi(b_x^(-1) n b_x),
L_y(e_x tensor v)=e_(y x) tensor v,
U(n b_y)=U(n) L_y.                                    (17)
```

The permutation `L_y` transports the displayed conjugate blocks exactly
as required by `b_y n b_y^(-1)`. Thus the multiplicative error of (17)
is bounded by the maximum error in the finite list of `N` microstates.
For `y!=1`, left translation has no fixed block, so the trace of
`U(n)L_y` is zero. For `y=1` and `n!=1`, all eight conjugates of `n`
are nontrivial, so their microstate traces tend to zero. This proves

```text
Q hyperlinear <=> N hyperlinear => V hyperlinear.       (18)
```

Being generated by eight hyperlinear subgroups is not a hyperlinearity
permanence theorem. Thus (14) does not prove the reverse implication
from `V` in (18).

There is also an important difference between hyperlinearity of the
whole group `Q` and a representation of `Q` into a hyperlinear group
that retains only `c`. Such a representation restricts nontrivially,
and therefore injectively, to `iota(V)`, because `c in iota(V)` and
`V` is simple. Hence it still implies hyperlinearity of `V`. It need
not be injective on `N` or `Q`.

## 6. The natural finite-edge amalgam cannot supply the third involution

Let `F=F_8=F_2[alpha]/(alpha^3+alpha+1)` and use the finite group
`G=SL_3(F)`. Fix

```text
c_G=(123),
y_1=x_12(alpha),       y_2=x_12(alpha^(-1)),
E=<y_1,y_2> ~= C_2^2.                                (19)
```

The coefficients `alpha` and `alpha^(-1)` are linearly independent over
`F_2`: they are nonzero and equality would give `alpha^2=1`, contrary
to the defining irreducible cubic. This proves the order-four assertion
in (19).

Evaluate the words in (1) that do not use `b_3` at `(c_G,y_1,y_2)`.
Since `alpha^(-1) alpha=1`, the same elementary commutator calculation
as in (7) gives

```text
d_G=x_13(1), h_G=x_32(1), a_G=x_12(1),
e_G=x_21(1), A_G=(12), D_G=(31).
```

In particular `d_G^2=(A_G c_G)^2=1`. The two matrices `A_G,c_G`
generate the permutation subgroup `S_G~=S_3`. In the copy of `V` from
(2), `A` and `c_V=D A` generate the corresponding subgroup `S_V~=S_3`.
Identify these marked subgroups and form

```text
M=G *_(S_G=S_V) V.                                   (20)
```

The vertex groups embed in this amalgam. It is a natural candidate for
extending an exact finite core by a putatively hyperlinear `V`: indeed
`M` is hyperlinear if and only if `V` is. For the forward implication
use subgroup closure. For the reverse implication, the group von
Neumann algebra is the tracial free product of `L(G)` and `L(V)` over
the finite-dimensional `L(S_3)`; the embeddability permanence result
in [Brown--Dykema--Jung, Corollary 4.5](https://arxiv.org/html/math/0609080v5#S4)
applies.

**Claim.** No element `z in M` commuting with both `y_1` and `y_2`
can complete the tuple `(c_G,y_1,y_2,z)` to a solution of the eight-word
packet. This holds even without assuming `z^2=1` in advance.

**Proof.** Consider the Bass--Serre tree of (20). The subgroup `E` fixes
the vertex `v_G` with stabilizer `G`. Every edge stabilizer is conjugate
to `S_3` and has order six. The order-four group `E` cannot lie in an
edge stabilizer. If `E` fixed any second vertex, it would fix every
edge on the path connecting the two fixed vertices, which is impossible.
Therefore

```text
Fix_tree(E)={v_G}.                                    (21)
```

An element centralizing `E` preserves its fixed-vertex set. Hence
`z v_G=v_G`, so `z in G`. All the compiled words `A,B,D` then belong
to the finite group `G`. If the eight-word packet held, the argument
of Section 1 would give a homomorphism

```text
V -> G,       A -> A_G=(12).
```

Every homomorphism from the infinite simple group `V` to a finite group
is trivial. This contradicts `A_G!=1`, proving the claim. QED.

The obstruction is to the original commuting involution, not merely to
the existence of the repaired `S_3`: the latter is already exact and
shared in (20). Centralization of `E` traps the missing generator in
the finite vertex group.

The proof applies to elements of the discrete amalgam `M`. It makes no
claim that the commutant of `E` inside `L(M)` has all its unitaries in
`L(G)`. That assertion would be stronger and is not supplied by a
fixed-point argument on a group tree. Nor does the proof exclude
different extensions, alterations of the first two involutions,
matrix amplifications, or arbitrary normalized-HS approximate models.

## 7. An exact criterion for finite permutation-wreath attempts

The split structure also identifies what a finite permutation-wreath
construction would have to solve. The following are equivalent:

1. There is a homomorphism `psi:N -> V` with `psi(c)!=1`.
2. There is a homomorphism `Theta:Q -> V^X semidirect F`, for some
   finite group `F` acting on a finite set `X` by permutations,
   with `Theta(c)!=1`.

For `1 => 2`, take the coordinate set and the acting group both equal
to `E_3`, and define

```text
f(n)_x=psi(b_x^(-1) n b_x),
Theta(n b_y)=(f(n),y).                                (22)
```

Let `y` act on functions by `(y.f)_x=f_(y^(-1)x)`. Since `E_3` is
abelian and every element is its own inverse, direct substitution gives
`f(b_y n b_y^(-1))=y.f(n)`. Thus (22) is a homomorphism. Its coordinate
at `x=1` detects `c`.

Conversely, the composition of a map in item 2 with the finite-group
projection kills `N`, by Section 4. Thus `Theta(N)` lies in the base
direct product. If `Theta(c)!=1`, at least one coordinate projection
restricts to a map `psi:N -> V` retaining `c`.

If `V` were hyperlinear, a map (22) would produce a hyperlinear target
retaining `c`: finite direct products preserve hyperlinearity, and so
do the finite extensions proved in Section 5. The existence of `psi`
in item 1 remains unproved. Neither this criterion nor the obstruction
in Section 6 establishes an equivalence between hyperlinearity of `V`
and feasibility of the eight-word packet.

The unfilled requirement is a simultaneous realization of the eight
Thompson copies with their actual shared Leavitt word identities, or a
uniform obstruction to such realizations. The individual `S_3` repair
and individual hyperlinearity of `V` do not supply that requirement.
