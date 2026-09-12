# Six circle-action generators for the Kirchberg alternative in STW Problem L

Date: 2026-09-05.

This manuscript gives six automorphism loops on a unital UCT Kirchberg algebra
with scaled graded K-theory `(Z^2, (1,0), Z^2)`, and proves that their homotopy
classes are an **integral basis** of its fundamental group. Each of these six
loops is a circle action. Four explicit products of them also give a basis
of the kernel of the rotation retraction in the earlier artifact.

The construction uses two specified finite graph models and one **fixed,
nonconstructively chosen unital classification isomorphism** between their
algebras. Transport to `A_theta tensor O_infinity` uses another fixed
classification isomorphism. No formula for either isomorphism on generators
is claimed. This is an answer to the Kirchberg alternative in the sense of
classification identifications contemplated in [STW, Section 14](https://arxiv.org/html/2506.10902v2#S14).
It does not construct six loops in the stably finite algebra `A_theta`.

## 1. The natural invariant, including injectivity

Let D be a unital UCT Kirchberg algebra with finitely generated free
K-groups and primitive unit `e_D=[1_D]` in K_0(D). For a based point-norm
continuous loop alpha define

\[
 \widehat\alpha:D\longrightarrow C(\mathbb T)\otimes D,
 \qquad \widehat\alpha(a)(z)=\alpha_z(a).
\]

Subtract the constant inclusion in KK and use the split evaluation
sequence at `1 in T`. This defines

\[
 \Delta_\alpha\in KK(D,SD)=KK^1(D,D).
\]

**Lemma 1.** The natural map is an isomorphism of abelian groups

\[
 \Delta:\pi_1(\operatorname{Aut}(D),\mathrm{id})
 \ \xrightarrow{\cong}\quad
 \operatorname{Hom}(K_1(D),K_0(D))
 \oplus\operatorname{Hom}(K_0(D)/\mathbb Ze_D,K_1(D)).             \tag{1}
\]

**Proof.** Dadarlat's Theorem 6.3, applied with `X=T`, identifies the
natural KK map up to a kernel; that kernel is

\[
 K_1(SD)/\operatorname{im}\bigl(KK(D,S^2D)\longrightarrow K_1(SD)\bigr)
 =K_0(D)/\operatorname{im}\bigl(KK(D,D)\xrightarrow{[1_D]^*}K_0(D)\bigr).
\]

The image on the right of the exact sequence is the unit-annihilating
part of `KK(D,SD)`, translated by the constant identity class. The
KK-continuity hypothesis holds because the circle is locally
contractible (Examples 5.4). The multiplication of reduced classes is
zero for the circle, so subtraction of the identity gives the additive
group law (Remark 6.4).
[Dadarlat, Theorem 6.3, Remark 6.4, and the definition of the kernel quotient before Theorem 3.6](https://www.math.purdue.edu/~mdd/Publications/Aut.pdf).

Here is why the kernel vanishes in the case at hand, a point not supplied
by merely counting ranks. Write `K_0(D)=Z e_D direct-sum H`. For every
`a in K_0(D)`, the homomorphism sending `e_D` to `a` and `H` to zero,
together with the zero endomorphism of K_1(D), lifts to KK(D,D) by the
UCT. Thus evaluation at the unit is onto. The Ext terms in the odd UCT
also vanish, since both domain K-groups are free. The unit-annihilation
condition is exactly `Delta(e_D)=0`, which yields (1). The UCT used
here is the theorem of
[Rosenberg--Schochet](https://doi.org/10.1215/S0012-7094-87-05524-4).

Dadarlat uses unbased homotopy classes of maps into the identity path
component. These agree here with based loop classes: a free homotopy
`H(z,t)` can be based by replacing it with `H(1,t)^{-1}H(z,t)`.
This completes the proof. \(\square\)

We use the Bott convention in which the loop `1+(z-1)p` has class `[p]`.
For a unitary w, the K_1-to-K_0 component of Delta is consequently the
Bott class of `z |-> alpha_z(w) w*`. A projection fixed throughout the
loop has zero reduced class. Delta is natural under conjugating by a
fixed isomorphism. These observations compute the invariant of the
actual loops below, rather than assigning abstract KK classes to
unspecified representatives.

## 2. A row construction in two finite graphs

For a positive integer vector `u=(u_1,...,u_n)`, let E(u) have vertices
`1,...,n`, a distinguished loop `d_i` at each vertex i, and edges
`a_{ij}^{(k)}:i -> j` for `1<=k<=u_j`. Rows of its adjacency matrix
are indexed by sources and columns by ranges:

\[
 M(u)_{ij}=\delta_{ij}+u_j,
 \qquad I-M(u)^t=-u\mathbf1^t.                                  \tag{2}
\]

Write p_i for its vertex projections and s_a for its edge partial
isometries. Our conventions are

\[
 s_a^*s_b=\begin{cases}p_{r(a)},&a=b,\\0,&a\ne b,\end{cases}
 \qquad \sum_{s(a)=i}s_as_a^*=p_i,
 \qquad \sum_i p_i=1.
\]

Order `sum_j(u_j+1)` columns by pairs `(j,k)` with `1<=k<=u_j+1`.
For each i form the following rectangular row over C*(E(u)):

\[
 (R_i)_{(j,k)}=
 \begin{cases}
 s_{a_{ij}^{(k)}},&k\leq u_j,\\
 s_{d_i},&k=u_j+1,\ j=i,\\
 p_j,&k=u_j+1,\ j\ne i.
 \end{cases}                                                   \tag{3}
\]

**Lemma 2.** All these rows satisfy `R_i R_i*=1` and
`R_i* R_i=P`, where P is the same diagonal projection, containing
`u_j+1` copies of p_j for each j. Hence `W_i=R_i R_n*` is a unitary
for `i<n`.

**Proof.** The edge entries in R_i have mutually orthogonal range
projections, and their sum is p_i. The other entries contribute one
p_j for each `j != i`. This gives `R_i R_i*=1`. Distinct entries
have zero adjoint product: this is the edge relation for two edges,
vertex orthogonality for two projections, and `p_j s_a=0` when
`j != s(a)` for the mixed case. The initial projection in column
`(j,k)` is always p_j. This proves the second equality. Multiplying
the row equalities gives `W_i W_i*=W_i* W_i=1`. \(\square\)

For `i<n` and any j, let `g_{ij,z}` multiply the one edge
`s_{a_{ij}^{(1)}}` by z and fix every other edge and every vertex.
This preserves every defining relation and has inverse `g_{ij,bar z}`.
It is a point-norm continuous circle action, first on the generators
and their polynomial algebra, then on the completed algebra by density
and isometry. It fixes R_n and all R_k with `k != i`. Equation (3)
therefore gives the exact identity

\[
 g_{ij,z}(W_k)W_k^*=
 \begin{cases}
 1+(z-1)s_{a_{ij}^{(1)}}s_{a_{ij}^{(1)}}^*,&k=i,\\
 1,&k\ne i.
 \end{cases}                                                   \tag{4}
\]

In particular,

\[
 \Delta_{g_{ij}}([W_k])=\delta_{ik}[p_j].                       \tag{5}
\]

The two graphs used below are finite, with strictly positive adjacency
matrices, and each vertex has at least two loop edges. They are strongly
connected and every cycle has an exit. Their algebras are simple and
purely infinite by [Bates--Pask--Raeburn--Szymanski, Section 5](https://nyjm.albany.edu/j/2000/6-14.pdf).
Finite graph algebras are separable, nuclear and UCT. For example, their
gauge crossed products are AF; stabilization and the dual Z action put
them in the bootstrap class. This is the rank-one case of
[Kumjian--Pask, Theorem 5.5](https://nyjm.albany.edu/j/2000/6-1.pdf).
The standard graph computation gives

\[
 K_0(C^*(E))=\operatorname{coker}(I-M^t),\qquad
 K_1(C^*(E))=\ker(I-M^t),                                      \tag{6}
\]

with the standard coordinate vectors representing the vertex
projections and the all-ones vector representing the unit.
[Drinen--Tomforde, Theorem 3.1](https://arxiv.org/pdf/math/0103036).

## 3. Four loops in the three-vertex model

Set `C=C*(E(1,1,2))`, so

\[
 M_C=\begin{pmatrix}2&1&2\\1&2&2\\1&1&3\end{pmatrix}.
\]

Equations (2) and (6) give

\[
 K_0(C)=\mathbb Z^3/\mathbb Z(1,1,2),\qquad K_1(C)\cong\mathbb Z^2.
\]

Put `e_C=[1_C]` and `b=[p_1]`. They are a basis of K_0(C), since

\[
 [p_1]=b,\qquad[p_2]=2e_C-b,\qquad[p_3]=-e_C.                  \tag{7}
\]

Equivalently the three columns `(1,1,2)`, `(1,1,1)`, `(1,0,0)`
have determinant -1. Put `U_1=R_1 R_3*` and `U_2=R_2 R_3*`.

These are an **integral** K_1 basis without any appeal to an
unspecified graph K_1 representative. Indeed, use (5) for j=3 and
apply minus the coefficient of e_C. The resulting two homomorphisms
from K_1(C) to Z take `[U_k]` to `delta_{ik}`. Thus the map from
Z^2 sending its basis to `[U_1],[U_2]` has a left inverse. Its image
is a direct summand of a free group of rank two, so its complement
is zero.

Define four circle actions

\[
 h_1(z)=g_{13,z^{-1}},\quad h_2(z)=g_{11,z},\quad
 h_3(z)=g_{23,z^{-1}},\quad h_4(z)=g_{21,z}.                    \tag{8}
\]

They fix the vertex projections, which generate K_0(C). Their
invariant table is

| Loop | Delta([U_1]) | Delta([U_2]) | Delta on K_0(C) |
| --- | --- | --- | --- |
| h_1 | e_C | 0 | 0 |
| h_2 | b | 0 | 0 |
| h_3 | 0 | e_C | 0 |
| h_4 | 0 | b | 0 |

They therefore span precisely the rank-four submodule
`Hom(K_1(C),K_0(C))` of (1).

## 4. A generator on the two-vertex model

Set `B=C*(E(1,2))`, with vertex projections p,q, so

\[
 M_B=\begin{pmatrix}2&2\\1&3\end{pmatrix}.
\]

The unit `e_B=[p]+[q]` generates K_0(B) and

\[
 K_0(B)=\mathbb Ze_B,\quad [p]=2e_B,\quad[q]=-e_B,
 \qquad K_1(B)\cong\mathbb Z.                                 \tag{9}
\]

Use (3) to form the two five-entry rows T_1,T_2 and put `V=T_1 T_2*`.
Let gamma_z multiply the edge `a_{12}^{(1)}` by `z^{-1}`, fixing
all other generators. Equation (4) shows

\[
 \gamma_z(V)V^*=1+(z^{-1}-1)s_{a_{12}^{(1)}}s_{a_{12}^{(1)}}^*,
 \qquad \Delta_\gamma([V])=-[q]=e_B.                           \tag{10}
\]

Since both groups in (9) are infinite cyclic, this proves that
`v=[V]` generates K_1(B) and Delta_gamma is the isomorphism sending
v to e_B. Its other component is zero, because gamma fixes the unit.

## 5. The two tensor-factor actions supply the missing directions

Let `A=B tensor B`, with minimal tensor product. This is a unital
UCT Kirchberg algebra. The
[torsion-free Kunneth theorem](https://msp.org/pjm/1982/98-2/p15.xhtml)
gives bases

\[
 K_0(A)=\mathbb Ze\oplus\mathbb Z\beta,
 \quad e=e_B\boxtimes e_B=[1_A],\quad\beta=v\boxtimes v,
\]
\[
 K_1(A)=\mathbb Zx\oplus\mathbb Zy,
 \quad x=v\boxtimes e_B,\quad y=e_B\boxtimes v.                \tag{11}
\]

Define actual circle actions

\[
 \rho_1(z)=\gamma_z\otimes\mathrm{id}_B,
 \qquad \rho_2(z)=\mathrm{id}_B\otimes\gamma_z.                 \tag{12}
\]

Their invariant table is

| Loop | Delta(x) | Delta(y) | Delta(beta) | Delta(e) |
| --- | --- | --- | --- | --- |
| rho_1 | e | 0 | y | 0 |
| rho_2 | 0 | e | -x | 0 |

For completeness, the sign is fixed as follows. Write t for the
positive generator of K_1(C(T)). Equation (10) means
`widehat(gamma)_*(v)=1 boxtimes v + t boxtimes e_B`, while
`widehat(gamma)_*(e_B)=1 boxtimes e_B`. Applying gamma to the
first factor of `v boxtimes v` produces the reduced term
`t boxtimes e_B boxtimes v`. Applying it to the second produces
`v boxtimes t boxtimes e_B`; moving the odd t past the odd v
gives `-t boxtimes v boxtimes e_B`. This proves both entries on
beta directly by the graded external-product rule.

## 6. Six loops on one algebra and the determinant-one certificate

The scaled graded K-groups of C and A agree. The unital
Kirchberg--Phillips classification theorem supplies an isomorphism
`psi:C -> A` realizing

\[
 e_C\mapsto e,\qquad b\mapsto\beta,\qquad
 [U_1]\mapsto x,\qquad[U_2]\mapsto y.                         \tag{13}
\]

Here both algebras are UCT Kirchberg and the unit is preserved, so
the hypotheses of classification hold. Fix this isomorphism once.
[Phillips, A Classification Theorem for Nuclear Purely Infinite Simple C*-Algebras](https://arxiv.org/abs/funct-an/9506010).

Define, for `1<=j<=4`,

\[
 \sigma_j(z)=\psi\circ h_j(z)\circ\psi^{-1}.                   \tag{14}
\]

**Theorem 3.** The six circle-action loops
`sigma_1,sigma_2,sigma_3,sigma_4,rho_1,rho_2` form a Z-basis of
`pi_1(Aut(A),id)`. In the order of coordinates

\[
 \bigl((\Delta x)_e,(\Delta x)_\beta,
       (\Delta y)_e,(\Delta y)_\beta,
       (\Delta\beta)_x,(\Delta\beta)_y\bigr),
\]

their columns are the matrix

\[
 L=\begin{pmatrix}
 1&0&0&0&1&0\\
 0&1&0&0&0&0\\
 0&0&1&0&0&1\\
 0&0&0&1&0&0\\
 0&0&0&0&0&-1\\
 0&0&0&0&1&0
 \end{pmatrix},\qquad \det L=1.                              \tag{15}
\]

**Proof.** Equations (8), (12), (13), and naturality give every
entry of (15). Its lower-right 2-by-2 block has determinant 1,
and its upper-left block is the 4-by-4 identity. Thus its columns
form a basis of the entire group on the right of (1). Lemma 1
identifies this group with the actual fundamental group. \(\square\)

An equivalent explicit spanning calculation is useful for checking
the integrality. If a class has coordinates `(a,b,c,d,f,g)`, then
its unique coefficients in the six-loop basis are

\[
 (a-g,\ b,\ c+f,\ d,\ g,\ -f).                              \tag{16}
\]

The preferred marking (13) is convenient but unnecessary for the
six-loop generation assertion. For **any** fixed unital
isomorphism psi, its four transported graph loops span the intrinsic
submodule `Hom(K_1(A),K_0(A))`. The two tensor actions project to
a basis of `Hom(K_0(A)/Z[1_A],K_1(A))`. These two facts already
prove generation and independence. There is no parameter-dependent
use of classification and no assumption that all six actions commute.

## 7. Four explicit loops in the canonical rotation-retraction kernel

Keep the marking (13) and form pointwise compositions

\[
 \kappa_1=\sigma_2,\quad \kappa_2=\sigma_4,\quad
 \kappa_3=\rho_1\sigma_1^{-1},\quad
 \kappa_4=\rho_2\sigma_3^{-1}.                               \tag{17}
\]

Each expression defines a based continuous automorphism loop.
The last two need not be circle actions. Since the fundamental
group of a topological group is abelian, pointwise composition and
inversion induce addition and negation on it. Formula (15) gives
the four columns

\[
 (0,1,0,0,0,0)^t,\quad (0,0,0,1,0,0)^t,\quad
 (0,0,0,0,0,1)^t,\quad (0,0,0,0,-1,0)^t.                     \tag{18}
\]

Now let `D=A_theta tensor O_infinity`. Choose the complement q to
`[1_D]` in K_0(D) used in the earlier rotation-retraction artifact;
write epsilon for the homomorphism with `epsilon([1_D])=1` and
`epsilon(q)=0`. The classes of the canonical unitaries
`U tensor 1, V tensor 1` are a basis of K_1(D). Indeed, in the
odd Pimsner--Voiculescu sequence, [U] is the injected circle K_1
generator and the boundary of the implementing unitary [V] is
plus or minus the circle's unit class. Tensoring by O_infinity
preserves these groups and generators. Fix a unital
classification isomorphism `chi:A -> D` with

\[
 e\mapsto[1_D],\quad\beta\mapsto q,\quad
 x\mapsto[U\otimes1],\quad y\mapsto[V\otimes1].                \tag{19}
\]

For the two-coordinate Bott-evaluation retraction r on D,
naturality shows that `r(chi alpha chi^{-1})` is precisely
`((Delta_alpha x)_e,(Delta_alpha y)_e)`. Thus (18) is an integral
basis of its kernel. The four loops

\[
 z\longmapsto\chi\kappa_j(z)\chi^{-1},\qquad j=1,2,3,4,        \tag{20}
\]

are the promised explicit basis of that kernel, expressed using
fixed classification identifications. Together with the two
canonical rotation loops `gamma tensor id` on D they form a basis
of `pi_1(Aut(D))`, by the already proved splitting of r. No
computation of the reduced K_0-to-K_1 invariant of the canonical
rotation loops is needed in this last step.

## 8. Scope, prior work, and verification

Problem L in [STW, Section 14](https://arxiv.org/html/2506.10902v2#S14)
asks for explicit generators in the rotation algebra or in its
Kirchberg counterpart and suggests dynamical models identified by
classification. Equations (8), (12), and (14) give six circle-action
generators for a Kirchberg model; (17)--(20) give the four missing
kernel generators beside the original rotation loops. These are
the precise assertions proved here.

The word "explicit" here allows fixed classification isomorphisms
between models. We supply all graph generators, edge phases,
unitaries, tensor actions, and their integer invariants. We do not
supply a generator-by-generator formula for psi or chi, a single
graph presentation in which all six actions have edge formulas, or
six loops in `Aut(A_theta)` itself. The weak homotopy equivalence
mentioned by STW does not provide explicit preimage loops in that
stably finite algebra. That remaining request is kept open in Cairn.

The imported homotopy-group theorem, graph K-theory, classification,
Bott periodicity, the UCT, and Kunneth are existing results, not
novelty claims. The contribution asserted in this manuscript is the
specific pair of finite graphs, the row unitaries that detect the
edge actions integrally, and their assembly into the full six-loop
basis and four-loop kernel basis.

A targeted literature check on 2026-09-05 found Problem L still
posed in the available STW version. The related
[Matsumoto--Sogabe, Reciprocal Cuntz--Krieger algebras, Section 7](https://arxiv.org/pdf/2502.18126)
computes gauge-action classes under reciprocal duality; it does not
give the six-loop construction above. This is a bounded search, not
a proof that no prior construction exists.

The standard-library script
`experiments/stw50_six_kirchberg_loops_check.py` verifies the graph
incidences and row supports, unimodular lattice bases, the reduced
invariant tables (including the graded sign), and the matrix inverse
and kernel basis over integers. These checks do not verify the
analytic classification or homotopy theorems. The latter are
explicit imports, and the new mathematical argument is the written
proof above. This manuscript has not undergone independent expert
review or proof-assistant verification.

Replay on 2026-09-05 passed all four exact certificate checks. The
isolated STW L Cairn component compiled cleanly (8 claims, 7 routes);
it derives the Kirchberg alternative and retains the stably finite
root as open. Full-repository `check --changed` and `preview`
encounter the same 55 pre-existing error diagnostics, with no added
errors, and the targeted duplicate review found none. Accordingly
the repository-wide generated frontier was left untouched. These
graph checks verify declarations and dependencies, not the proof.
