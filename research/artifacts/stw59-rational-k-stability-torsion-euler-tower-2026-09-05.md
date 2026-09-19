# A rationally K-stable simple unital AH tower with a persistent torsion kernel

Date: 5 September 2026. Complete proof, internally reviewed.
The coordinating review checked the integral Euler identity, all-class
fourth-power vanishing, torsion-valued Thom product, actual connecting
maps, and the primary-source evaluation argument for rational stability.
No external review, formal verification, or literature priority is
claimed. This concerns rational versus integral
K-stability; it is not an additional claimed solution of STW LIX.

**Abstract.** We construct a simple unital monotracial AH algebra
which is rationally K-stable but has a nonzero integral stabilization
kernel of order two. Its homogeneous building blocks are endomorphism
algebras of vector bundles over compact finite CW complexes. This answers
negatively the question raised by Vaidyanathan about extending the
equivalence of rational and integral K-stability from AT to AH
algebras. The proof uses an integral Euler formula and a fourth-power
identity in mod-two cohomology, which controls all K-theory classes
without a line-bundle generation assumption.

## 1. The theorem

There is a simple unital separable nuclear stably finite AH algebra \(A\)
which is rationally K-stable and for which

\[
\ker\bigl(U(A)/U_0(A)\longrightarrow K_1(A)\bigr)
\cong\mathbb Z/2.
\tag{1.1}
\]

In particular \(A\) is not K-stable, and not \(K_1\)-injective.
Its matrix algebra \(M_2(A)\) is K-stable. The construction has a
unique tracial state.

Here rational K-stability has exactly the Seth--Vaidyanathan
[Definition 1.3](https://arxiv.org/pdf/2102.13529) convention:
every matrix inclusion induces an isomorphism on \(\pi_m\) of the identity
component after tensoring with \(\mathbb Q\), for every \(m\ge1\).
Integral K-stability also includes \(\pi_0\). We do not assert
\(K_1(A)=0\) or identify the whole component group \(U(A)/U_0(A)\).

The distinguishing ingredient is a fourth-power identity for the
integral Euler map after reduction modulo two. It applies to arbitrary
\(K^0\) classes, including classes arising from Künneth Tor terms.

## 2. The integral Euler formula, with torsion coefficients retained

Let \(X\) be a connected finite CW complex of dimension \(2r\), and
\(E\) a rank-\(r\) complex vector bundle. Write \(\mathcal G(E)\)
for its unitary gauge group, and \(\mathcal S(E\oplus\mathbf1)\)
for the space of unit sections of \(E\oplus\mathbf1\). The gauge fibration

\[
\mathcal G(E)\longrightarrow\mathcal G(E\oplus\mathbf1)
\longrightarrow\mathcal S(E\oplus\mathbf1)
\tag{2.1}
\]

is the locally trivial principal bundle sending a unitary to its
action on the last constant unit vector. Local polar-decomposition
lifts and the stable comparison are proved in Sections 2--3 of
[the exact factorial calculation](stw59-exact-factorial-component-groups-2026-09-05.md).
Those arguments do not require torsion-free cohomology or \(K^1(X)=0\).
The fiber sphere is \(S^{2r+1}\); its orientation local system is trivial.
Consequently

\[
\begin{aligned}
\pi_0\mathcal S(E\oplus\mathbf1)&=0,&
\pi_1\mathcal S(E\oplus\mathbf1)&\cong H^{2r}(X;\mathbb Z),\\
\pi_1\mathcal G(E\oplus\mathbf1)&\cong K^0(X),&
\pi_0\mathcal G(E\oplus\mathbf1)&\cong K^1(X).
\end{aligned}
\]

The exact sequence therefore gives

\[
K^0(X)\xrightarrow{\Lambda_E}H^{2r}(X;\mathbb Z)
\xrightarrow{\partial}\pi_0\mathcal G(E)
\longrightarrow K^1(X)\longrightarrow0.
\tag{2.2}
\]

The stable arrow is the actual matrix-stabilization arrow under the
usual Morita identification. Stabilizing by trivial lines or by copies
of E gives the same map: embed E in a trivial bundle, add its
complement, and use the standard rotation homotopy. In particular,

\[
\ker\bigl(\pi_0\mathcal G(E)\longrightarrow K^1(X)\bigr)
\cong H^{2r}(X;\mathbb Z)/\operatorname{im}\Lambda_E.
\tag{2.3}
\]

For a virtual complex vector bundle \(\beta\), let \(s_k(\beta)\)
be its integral Newton power-sum class, and put
\(s_0(\beta)=\operatorname{rank}(\beta)\). For \(k\ge1\) these
are additive integral characteristic classes characterized under the
splitting principle by
\[
s_k\left(\sum_a L_a-\sum_b M_b\right)
=\sum_a c_1(L_a)^k-\sum_b c_1(M_b)^k.
\]
The exact integral formula is
\[
\Lambda_E(\beta)
=\sum_{j=0}^{r}c_j(E)(-1)^{r-j}s_{r-j}(\beta).
\tag{2.4}
\]

We justify (2.4) integrally rather than infer it from a rational
Chern-character calculation. Let \(H\) be the Bott line on \(S^2\),
and \(t=c_1(H)\), with \(t^2=0\). A gauge loop at rank \(r+1\)
has a clutched bundle \(W\) over \(S^2\times X\) whose stable class is
\[
[W]=[E\oplus\mathbf1]+([H]-1)\beta.
\]
Its section obstruction is \(c_{r+1}(W)\), and slant product with
\([S^2]\) is \(\Lambda_E(\beta)\), up to the fixed orientation sign.
After pulling back to the flag bundles of representatives of the
positive and negative parts of \(\beta\), their Chern roots are integral
classes. These pullbacks are injective on integral cohomology by the
splitting principle, including in the presence of torsion.
For one line with root \(x\),
\[
c\bigl(([H]-1)[L_x]\bigr)
=\frac{1+x+t}{1+x}=1+\frac{t}{1+x}.
\]

Products for positive roots and inverse products for negative roots,
using \(t^2=0\), give
\[
c\bigl(([H]-1)\beta\bigr)
=1+t\sum_{k\ge0}(-1)^k s_k(\beta).
\]
Multiply by \(c(E)\), and take the coefficient of \(t\) in
\(c_{r+1}\).
This proves (2.4). In particular it is valid on every \(K^0\) class;
no assertion that \(K^0(X)\) is generated by line bundles is needed.

Modulo two, the splitting principle also proves

\[
s_{4k}(\beta)=s_k(\beta)^4\quad\text{in mod-two cohomology},
\qquad k\ge1.
\tag{2.5}
\]

For \(k=0\) the same equality holds after interpreting \(s_0\) as
rank modulo two. If \(E=F^{\oplus4}\), with
\(\operatorname{rank}(F)=m\) and \(r=4m\), then
\(c(E)=c(F)^4\) modulo two, and (2.4)--(2.5) yield
\[
\rho_2\bigl(\Lambda_E(\beta)\bigr)
=\left(\sum_{j=0}^{m}c_j(F)s_{m-j}(\beta)\right)^4
\quad\text{in }H^{8m}(X;\mathbb F_2).
\tag{2.6}
\]
Here \(\rho_2\) denotes reduction modulo two, and the classes inside
the parentheses are reduced modulo two as well.

This is an identity of characteristic classes, not a computation on
a selected subgroup of \(K^0(X)\).

## 3. The spaces, bundles, and fourth-power vanishing

Set

\[
\begin{aligned}
r_i&=4\cdot2^i,&X_0&=(\mathbb{RP}^{2})^4,\\
X_i&=X_0\times\prod_{j=0}^{i-1}\mathbb{RP}^{2r_j},&
E_i&=\mathbf1^{\oplus4}\oplus
       \bigoplus_{j=0}^{i-1}L_{j+1}^{\oplus r_j}.
\end{aligned}
\]

where \(L_{j+1}\) is the complexification of the real tautological
line from \(\mathbb{RP}^{2r_j}\). Thus
\[
\dim X_i=2r_i,\qquad\operatorname{rank}(E_i)=r_i,\qquad
E_i=F_i^{\oplus4},\qquad
F_i=\mathbf1\oplus\bigoplus_{j=0}^{i-1}L_{j+1}^{\oplus2^j}.
\tag{3.1}
\]

Each even-dimensional real projective space \(\mathbb{RP}^{2n}\)
has positive integral cohomology \(\mathbb Z/2\) in even degrees
\(2,\ldots,2n\) and zero in odd degrees. Its top class is
\(c_1(L)^n\). Its reduced rational cohomology
vanishes. Integral Künneth in top degree, or directly the top
cellular cochain group and its preceding differential, gives

\[
H^{2r_i}(X_i;\mathbb Z)\cong\mathbb Z/2.
\tag{3.2}
\]

The product of the top integral classes is a generator. In top
degree there are no Künneth Tor summands: such a summand would
require a sum of factor degrees one above the total dimension.
The coefficient sequence
\(\mathbb Z\xrightarrow{2}\mathbb Z\to\mathbb F_2\)
shows that reduction
\[
H^{2r_i}(X_i;\mathbb Z)
\xrightarrow{\rho_2}H^{2r_i}(X_i;\mathbb F_2)
\tag{3.3}
\]

is injective, since multiplication by two on its domain is zero.

The full mod-two cohomology ring of \(X_i\) is the tensor product of
the truncated polynomial rings of its factors, with degree-one
generators. In particular

\[
H^*(X_0;\mathbb F_2)
=\mathbb F_2[x_1,x_2,x_3,x_4]/(x_1^3,x_2^3,x_3^3,x_4^3),
\qquad |x_j|=1.
\]

Every fourth power of a class on \(X_i\) has degree zero in the \(X_0\)
factor: in characteristic two fourth powers distribute over sums,
and a monomial with positive \(X_0\)-degree has fourth power zero.
But a class in total degree \(\dim X_i\) with degree zero in \(X_0\)
must vanish, since the remaining factors have dimension \(\dim X_i-8\).
Thus (2.6) and (3.3) prove

\[
\Lambda_{E_i}(\beta)=0
\qquad\text{for every }\beta\in K^0(X_i).
\tag{3.4}
\]

Combining (2.3) and (3.4), at every stage

\[
\ker\bigl(\pi_0\mathcal G(E_i)\longrightarrow K^1(X_i)\bigr)
\cong\mathbb Z/2.
\tag{3.5}
\]

The possible Künneth Tor contributions to \(K^1(X_i)\), and to
\(K^0(X_i)\), have not been suppressed. Equation (3.5) identifies the
kernel, and (3.4) handles all possible Euler relations.

## 4. Integral propagation of the kernel

We need a relative Euler product statement, valid on finite CW
complexes with torsion cohomology. Let \(X\) have dimension \(2r\),
\(\operatorname{rank}(E)=r\), let \(Y\) have dimension \(2n\), and
let \(J\) be a rank-\(n\) complex bundle on \(Y\). Put
\(E'=\operatorname{pr}_X^*E\oplus\operatorname{pr}_Y^*J\)
on \(X\times Y\).
Extension by the identity gives a map of the gauge fibrations

\[
\begin{array}{ccccc}
\mathcal G(E)&\longrightarrow&\mathcal G(E\oplus\mathbf1)
&\longrightarrow&\mathcal S(E\oplus\mathbf1)\\
\downarrow&&\downarrow&&\downarrow\\
\mathcal G(E')&\longrightarrow&\mathcal G(E'\oplus\mathbf1)
&\longrightarrow&\mathcal S(E'\oplus\mathbf1).
\end{array}
\]

Its right arrow is \(s\mapsto(\operatorname{pr}_X^*s,0)\).
On the fundamental groups
of the section spaces, identified with top integral cohomology,
this sends

\[
\alpha\longmapsto
\operatorname{pr}_X^*\alpha\smile\operatorname{pr}_Y^*c_n(J).
\tag{4.1}
\]

Here is a cohomological proof, avoiding oriented-manifold counts.
A section loop \(s\) of \(E\oplus\mathbf1\) is a nowhere-zero
boundary section over \((D^2\times X,S^1\times X)\).
Its relative Euler obstruction is the suspension of \(\alpha\).
After crossing with \(Y\), the boundary section \((s,0)\) has
relative Euler obstruction equal to this class times c_n(J).
Indeed, extend \(s\) to an arbitrary section \(S\) on \(D^2\times X\),
choose a section \(\sigma\) of \(J\), and choose a nonnegative
function \(\chi\) on \(D^2\)
which is zero on its boundary and positive in its interior.
The section \((S,\chi\sigma)\) extends \((s,0)\). The product formula for
the Thom classes of a direct sum, followed by pullback by this
section, identifies its relative Euler class with the stated
cup product. This argument uses oriented complex bundle Thom
classes over the base pair, and does not require that X or Y
be orientable manifolds. Removing the suspension proves (4.1).
Naturality of the boundary map in (2.2) then gives (4.1) on the
kernel quotients.

For our tower take \(Y=\mathbb{RP}^{2r_i}\), \(n=r_i\), and
\(J=L^{\oplus r_i}\). Then \(c_{r_i}(J)=c_1(L)^{r_i}\) is the
nonzero top integral class of \(Y\).
The external product with it sends the generator of (3.2) to
the generator at stage i+1. Thus extension by 1_J maps the two
kernels in (3.5) isomorphically.

## 5. The actual unital connecting maps and simplicity

Put \(A_i=\Gamma(X_i,\operatorname{End}(E_i))\). Choose points
\(x_i\in X_i\) with dense projected tails: for each \(k\), the
projections to \(X_k\) of \(x_i\), \(i\ge k\), are dense in
\(X_k\), and remain dense after deleting any
finite initial segment. Such a sequence is obtained by enumerating
the countable collection of basic open sets at all stages and
repeating every requirement infinitely often.

Fix an identification \((E_i)_{x_i}\cong\mathbb C^{r_i}\).
The actual maps are
\[
\phi_i(a)=\operatorname{pr}_{X_i}^*a\oplus
                  \bigl(a(x_i)\otimes1_L\bigr).
\tag{5.1}
\]
They are injective and unital maps into \(A_{i+1}\), using
\(E_{i+1}=\operatorname{pr}_{X_i}^*E_i\oplus L^{\oplus r_i}\).

Their action on component kernels agrees with Section 4. To
make this explicit, any representative \(u\in\mathcal G(E_i)\)
can be replaced within its component by a representative satisfying
\(u(x_i)=1\). Choose a selfadjoint logarithm of \(u(x_i)^*\) in
the matrix fiber, extend it to a selfadjoint section \(h\) of
\(\operatorname{End}(E_i)\) using a local trivialization and a
cutoff function, and replace \(u\) by \(\exp(ih)u\).
For this representative (5.1) is exactly

\[
\phi_i(u)=\operatorname{pr}_{X_i}^*u\oplus1_J.
\]

Therefore its component is the image under the gauge-fibration
map of Section 4. This reasoning imposes no contractibility
condition on evaluation of a chosen gauge loop or stable
nullhomotopy at x_i; those loops can be noncontractible.
It proves that the nonzero kernel component survives every
actual connecting map.

Let \(A\) be the inductive limit. Each \(A_i\) is a unital homogeneous
corner over a finite CW complex, so \(A\) is separable, nuclear,
and AH in the compact-building-block sense. The pullback
summands make all maps injective. If \(a\) is a nonzero positive
element at stage \(k\), some later \(x_i\) projects into an open set
where \(a\) is nonzero. The retained pullback summand makes
\(\phi_{k,i}(a)(x_i)\) nonzero. Its evaluation summand at the next
stage is nonzero at every point of \(X_{i+1}\). Consequently the
image of \(a\) at that stage is full. This standard ideal test for
injective inductive limits proves simplicity.

Tracial states on \(A_i\) are probability measures on \(X_i\) composed
with normalized fiber trace. Pullback along (5.1) sends a
probability measure \(\mu\) on \(X_{i+1}\) to

\[
\mu\longmapsto
\tfrac12(\operatorname{pr}_{X_i})_*\mu+\tfrac12\delta_{x_i}.
\]

The diameter of the images of the trace spaces at a fixed
stage contracts by a factor at most \(2^{-l}\) after \(l\) steps.
Compactness gives existence and this estimate gives uniqueness
of a compatible trace. Its trace on the simple limit is faithful,
so \(A\) is stably finite. The constant trivial line in \(E_i\)
gives a projection of trace \(1/r_i\) in \(A\); these traces tend
to zero, so \(A\) is infinite-dimensional.

Both \(\pi_0\) of the unitary group and \(K_1\) are continuous for these
inductive limits. Concretely, a unitary and any compact
parameter family of unitaries in the limit are approximated
at a common finite stage and corrected by polar decomposition;
nearby unitaries are joined by the logarithm path. Thus a
nonzero component cannot disappear without disappearing at
some finite stage. Equations (3.5) and (4.1) give an injective
\(\mathbb Z/2\) in the limit stabilization kernel.

They also identify the whole kernel. If a component in the
limit has stable class zero, represent it at a finite stage.
Its \(K_1\) class becomes zero at some later stage by continuity
of \(K_1\). At that stage it belongs to the kernel in (3.5), which has
exactly two elements. Both persist. Hence (1.1) holds.

## 6. Rational K-stability: the actual stabilization maps

We use the primary result of Klein--Schochet--Smith,
*Continuous trace C*-algebras, gauge groups and rationalization*,
Theorem 5.6 and its proof, together with Proposition 5.1 and
the fiberwise construction in Lemma 9.1/Corollary 9.2:
[primary manuscript](https://arxiv.org/pdf/0811.0771).

For a rank-\(N\) bundle \(V\) over a connected rationally acyclic
finite CW complex \(X\), evaluation at a point gives an isomorphism
\[
\pi_m\mathcal G(V)\otimes\mathbb Q
\xrightarrow{\ \cong\ }\pi_m U(N)\otimes\mathbb Q,
\qquad m\ge1.
\tag{6.1}
\]

For clarity, this statement concerns the evaluation map itself,
not only an abstract agreement of group dimensions. The cited
fiberwise Gottlieb construction identifies it with the loop of
evaluation \(\operatorname{Map}(X,BU(N);f)\to BU(N)\), at the
bundle classifying map \(f\).
Proposition 5.1 rationalizes the mapping-space component by
rationalizing its target. Since

\[
BU(N)_{\mathbb Q}\simeq\prod_{j=1}^{N}K(\mathbb Q,2j),
\]

the homotopy groups of its mapping space are sums of
\(H^{2j-k}(X;\mathbb Q)\), and evaluation retains \(H^0\).
Rational acyclicity
makes it an isomorphism in every positive degree; looping gives
(6.1). The constructions commute with restriction to a point.

Every \(X_i\) in Section 3 is rationally acyclic by the rational
Künneth theorem. For any fixed \(m\ge1\) and matrix index \(l\ge2\),
the evaluation square for the actual inclusion

\[
U(M_{l-1}(A_i))\longrightarrow U(M_l(A_i))
\]

has vertical rational isomorphisms (6.1), and bottom arrow

\[
U((l-1)r_i)\longrightarrow U(lr_i),
\qquad v\longmapsto\operatorname{diag}(v,1).
\]

Once \(m<2r_i\), this is an isomorphism on \(\pi_m\) (and hence
rationally) by the usual unitary stable range. For each fixed
\(m,l\) it is therefore an isomorphism at all sufficiently late
stages. Naturality with respect to (5.1), continuity of positive
homotopy groups under C*-inductive limits, and exactness of
tensoring with \(\mathbb Q\) prove rational K-stability of \(A\).

This argument proves a more general useful fact: any inductive
limit of endomorphism algebras over connected rationally acyclic
finite CW bases, whose bundle ranks tend to infinity, is
rationally K-stable. No compatibility of chosen evaluations
with the inductive maps is required; the relevant commuting
diagrams are the matrix-stabilization diagrams at each stage.

## 7. Matrix stabilization and scope

For completeness, \(M_2(A)\) is integrally K-stable. At stage \(i\)
its bundle rank is \(2r_i\) while its base has dimension \(2r_i\).
Adding one trivial line has unit-section fiber \(S^{4r_i+1}\).
Its section space is \(2r_i\)-connected, so the gauge inclusion
is an isomorphism on \(\pi_m\) whenever \(m\le2r_i-1\).
Subsequent additions
have at least this range. Comparison with matrix stabilization
uses the same complement-and-rotation identification as in
Section 2. The range tends to infinity; passing to the
inductive limit proves all matrix-stabilization maps for \(M_2(A)\)
are isomorphisms in every fixed degree, including degree zero.

In particular the element of order two in (1.1) is killed by
the first matrix amplification. Its integral obstruction is
compatible with rational K-stability, which ignores \(\pi_0\) and
only tests positive-degree groups after rationalization.

The known Seth--Vaidyanathan
[Example 2.1](https://arxiv.org/pdf/2102.13529) uses the nonunital
commutative algebra \(C_0(\mathbb{RP}^2\setminus\{x_0\})\).
Their [AT Theorem A](https://arxiv.org/pdf/2203.00979)
proves rational and integral K-stability equivalent for AT
algebras. Vaidyanathan raises the corresponding general AH
question in Section 20, printed page 48, of
[the operator-algebra compendium](https://www.isibang.ac.in/~jay/papers/oaotINSA.pdf).
Seth's 2026 Corollary 3.10 proves K-stability for all simple
unital infinite-dimensional diagonal AH algebras in the
globally trivial matrix-bundle sense:
[primary manuscript](https://arxiv.org/pdf/2512.04780).
The present system uses twisted bundles and is not covered by
that theorem. No broader novelty or priority conclusion is
drawn from this bounded literature comparison.

The proof-critical points checked in the coordinating review are the
integral identity (2.4), its fourth-power consequence (2.6),
the torsion-valued relative Euler product (4.1), and the
naturality of evaluation used in (6.1). The finite-stage kernel
and the full component group must remain distinguished.
