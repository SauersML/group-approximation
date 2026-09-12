# Every finite cyclic group as the entire unitary component group of a simple AH algebra

Date: 2026-09-05. **Complete proof; internal mathematical review completed
5 September 2026; not externally peer reviewed or formally verified.**
This strengthens the factorial family to arbitrary finite cyclic groups.
It is not a second named open-problem solution or a claim of external verification.

## 1. The theorem

**Theorem.** For every integer \(d\ge2\), there is a separable,
simple, unital, nuclear, stably finite, infinite-dimensional AH
algebra \(A_d\) such that
\[
K_1(A_d)=0,\qquad
U(A_d)/U_0(A_d)\cong\mathbb Z/d.
\tag{1.1}
\]
There is an explicit initial unitary whose image generates the
entire group, and its first matrix stabilization is null-homotopic.

The initial base is
\[
X_0=S^2\times\mathbb{CP}^{d-1},
\]
with trivial rank-\(d\) bundle. Subsequent stages add the same
tautological-line evaluation blocks as in the factorial construction.
The extra projective factor in \(X_0\) changes the image of the
gauge-group Euler map from \(d!\mathbb Z\) to \(d\mathbb Z\).

## 2. The gauge-group calculation used below

We recall precisely the dimension-dependent calculation from
[the exact factorial component-group proof](stw59-exact-factorial-component-groups-2026-09-05.md),
Sections 2–4.

Let \(X\) be a connected closed oriented \(2r\)-dimensional
finite CW complex with \(K^1(X)=0\), and let \(E\) be a
complex rank-\(r\) bundle. Let \(\mathcal G(E)\) be its
unitary gauge group. The bundle \(F=E\oplus\mathbf1\)
has the gauge/section fibration
\[
\mathcal G(E)\longrightarrow\mathcal G(F)
\longrightarrow\mathcal S(F).
\tag{2.1}
\]
The sphere fiber is \(S^{2r+1}\), so
\[
\pi_0\mathcal S(F)=0,\qquad
\pi_1\mathcal S(F)\cong H^{2r}(X;\mathbb Z)\cong\mathbb Z.
\]
One further trivial-line addition gives a \(2\)-connected
section space. Thus \(\pi_0\mathcal G(F)\) and
\(\pi_1\mathcal G(F)\) are already stable:
\[
\pi_0\mathcal G(F)=K^1(X)=0,\qquad
\pi_1\mathcal G(F)\cong K^0(X).
\]
The preceding proof justifies these identifications explicitly
by adding a complementary bundle and rotating the two copies
of \(F\); it does not assume that \(F\) itself is trivial.

The exact sequence consequently gives
\[
\pi_0\mathcal G(E)\cong\mathbb Z/\operatorname{im}\Lambda_E,
\tag{2.2}
\]
where
\[
\Lambda_E(\beta)=
\left\langle
\sum_{j=0}^{r}
(-1)^{r-j}(r-j)!\,
c_j(E)\operatorname{ch}_{r-j}(\beta),
[X]\right\rangle.
\tag{2.3}
\]
The overall sign depends on a single orientation convention
and does not affect (2.2).

For clarity, the integral normalization is as follows.
A loop \(g\) in \(\mathcal G(F)\) clutches a rank-\((r+1)\)
bundle \(W_g\) over \(S^2\times X\). Its virtual difference
from \(F\) is
\[
[W_g]-[F]=([\ell]-1)\beta,
\]
where \(c_1(\ell)\) generates \(H^2(S^2;\mathbb Z)\).
The integer of the section loop \(g e\) is the relative
Euler number on \(D^2\times X\), and hence the top Chern
number of \(W_g\). Since
\[
\operatorname{ch}([W_g]-[F])
=c_1(\ell)\operatorname{ch}(\beta),\qquad c_1(\ell)^2=0,
\]
the Newton identity yields (2.3). Every \(\beta\) is
realized by an actual loop at rank \(r+1\), by the
stable-range isomorphism above. These arguments depend
only on the indicated dimension, orientation, and
\(K^1\)-vanishing assumptions, not on a sphere-product
description of \(X\).

## 3. Exact finite-stage groups of order \(d\)

Fix a product
\[
Y=\prod_{j=1}^{\ell}\mathbb{CP}^{e_j},
\qquad m=\sum_je_j,\qquad
H=\bigoplus_{j=1}^{\ell}L_j^{\oplus e_j},
\]
allowing the empty product. Set
\[
X=S^2\times\mathbb{CP}^{d-1}\times Y,\qquad
E=\mathbf1^d\oplus H,\qquad r=d+m.
\tag{3.1}
\]
Then \(\dim_{\mathbb R}X=2r\). All cells are even-dimensional,
so \(K^1(X)=0\). Let \(L_0\) denote the tautological line
on the distinguished \(\mathbb{CP}^{d-1}\) factor and put
\[
h_0=c_1(L_0),\qquad h_j=c_1(L_j).
\]

Let \(\kappa\in\widetilde K^0(S^2)\) have Chern character
\(x\), an integral generator of \(H^2(S^2;\mathbb Z)\).
The projective-space \(K\)-ring and torsion-free Künneth
theorem decompose every \(\beta\in K^0(X)\) as
\[
\beta=\beta_0+\kappa\beta_1,
\qquad
\beta_0,\beta_1\in K^0(\mathbb{CP}^{d-1}\times Y).
\tag{3.2}
\]
Only the second summand contributes to (2.3), since
\(c_j(E)=c_j(H)\) is pulled back from \(Y\).

The coefficient group in (3.2) is additively generated
by line monomials
\[
\beta_1=L_0^a\prod_jL_j^{a_j}.
\]
For such a monomial,
\[
\operatorname{ch}(\kappa\beta_1)
=x\exp\Bigl(a h_0+\sum_j a_jh_j\Bigr).
\]
In (2.3), only \(0\le j\le m\) can contribute.
Put \(k=m-j\). To pair with \([X]\), a term must contain
\(h_0^{d-1}\) and a \(Y\)-monomial of degree \(2k\)
before multiplication by \(c_j(H)\). Its numerical
coefficient is
\[
\pm
\frac{(d+k)!}{(d-1)!\prod_\nu b_\nu!}
a^{d-1}\prod_\nu a_\nu^{b_\nu},
\qquad \sum_\nu b_\nu=k.
\tag{3.3}
\]
The factorial quotient is
\[
\frac{(d+k)!}{(d-1)!\prod_\nu b_\nu!}
=
d\binom{d+k}{d,b_1,\ldots,b_\ell},
\tag{3.4}
\]
an integral multiple of \(d\). Multiplication by the
integral class \(c_j(H)\) and taking integer linear
combinations preserve divisibility. Since the
cohomology is torsion-free, this is integral
divisibility:
\[
\operatorname{im}\Lambda_E\subset d\mathbb Z.
\tag{3.5}
\]

For the reverse inclusion choose
\[
\beta=\kappa L_0.
\]
There is no positive-degree \(Y\)-part in its Chern
character. Consequently only \(j=m\) contributes,
and (2.3) gives
\[
\Lambda_E(\kappa L_0)
=
(-1)^d\frac{d!}{(d-1)!}
\left\langle x h_0^{d-1}c_m(H),[X]\right\rangle
=\pm d.
\tag{3.6}
\]
Here \(c_m(H)=\prod_jh_j^{e_j}\) has top Chern number
of absolute value one. Equation (3.6) is realized by
an actual loop of gauge transformations, as explained
in Section 2. Thus
\[
\operatorname{im}\Lambda_E=d\mathbb Z,\qquad
\boxed{\ \pi_0\mathcal G(E)\cong\mathbb Z/d.\ }
\tag{3.7}
\]

## 4. The initial generator

For \(Y\) a point, the base is
\(X_0=S^2\times\mathbb{CP}^{d-1}\) and
\(E_0=\mathbf1^d\). Its even-cell decomposition has
one top cell. Collapsing the lower skeleton gives
a based map
\[
c:X_0\longrightarrow S^{2d}
\]
of degree one, after choosing orientations consistently.

Fix
\[
u_d:S^{2d}\to U(d)
\]
to be the boundary of the degree-one sphere class
in the fibration
\[
U(d)\longrightarrow U(d+1)\longrightarrow S^{2d+1}.
\]
By Bott's unstable calculation, its class generates
\(\pi_{2d}(U(d))\cong\mathbb Z/d!\). Define
\[
v_0=u_d\circ c\in U(C(X_0,M_d)).
\tag{4.1}
\]

We verify that (4.1) generates the group \(\mathbb Z/d\)
in (3.7); order \(d!\) on the sphere alone would not
justify this assertion.

Pullback along \(c\) gives a commuting diagram of
the gauge/section fibrations for the trivial bundles
over \(S^{2d}\) and \(X_0\). Their section-space
fundamental groups identify with
\(H^{2d}(S^{2d};\mathbb Z)\) and
\(H^{2d}(X_0;\mathbb Z)\). The induced map is \(c^*\),
which is multiplication by one. Naturality of the
boundary maps therefore identifies the class of
\(u_d\circ c\) with the boundary of \(1\in\mathbb Z\)
for \(X_0\). In the quotient description (3.7), this
is precisely a generator.

Also \(u_d\oplus1\) contracts in \(U(d+1)\).
Thus the first matrix stabilization of \(v_0\) is
null-homotopic, by leaving the unused \(d-1\)
trivial directions fixed.

## 5. Generator transport under a new line-bundle block

The necessary naturality is not ordinary pullback
alone: the rank and dimension both increase. We give
the Euler calculation explicitly.

Suppose \(X,E\) are as in (3.1), with
\(\operatorname{rank}E=r\), and set
\[
Z=\mathbb{CP}^r,\qquad J=L^{\oplus r},\qquad
X'=X\times Z,\qquad E'=\operatorname{pr}_X^*E\oplus J.
\]
Then \(\operatorname{rank}E'=2r\) and \(\dim X'=4r\).
Extension by the identity gives a continuous group
homomorphism
\[
\psi:\mathcal G(E)\to\mathcal G(E'),\qquad
g\longmapsto\operatorname{pr}_X^*g\oplus1_J.
\tag{5.1}
\]
The same extension on \(F=E\oplus\mathbf1\), after
reordering the trivial line, and the section map
\[
s\longmapsto(\operatorname{pr}_X^*s,0)
\tag{5.2}
\]
give a commuting diagram of gauge/section fibrations.

**Lemma.** Under the relative-Euler identifications of
their section-space fundamental groups with \(\mathbb Z\),
the map (5.2) is multiplication by
\[
\left\langle c_r(J),[Z]\right\rangle=\pm1.
\tag{5.3}
\]

**Proof.** Represent a based section loop by its
boundary section on \(S^1\times X\). Extend it as a
section \(S\) of the pullback of \(F\) over \(D^2\times X\),
allowing zeros. This bundle has real rank \(2r+2\),
equal to the dimension of the base. Choose an extension
transverse to zero in the interior and nonvanishing
near the boundary. Its signed zero count is the
integer of the original loop.

Choose a transverse section \(\sigma\) of \(J\) over
\(Z\), and a scalar function \(\chi\) on \(D^2\) which
vanishes near its boundary and is positive at the
disk coordinates of all zeros of \(S\). On
\(D^2\times X\times Z\), use
\[
\widetilde S(x,t,z)=
\bigl(S(x,t),\,\chi(t)\sigma(z)\bigr).
\tag{5.4}
\]
The boundary is exactly (5.2). Its zeros are the
products of zeros of \(S\) and zeros of \(\sigma\).
Their derivatives are block triangular with invertible
diagonal blocks, so their orientation signs multiply.
The new relative Euler number is therefore the old
one times the top Chern number of \(J\), proving (5.3).

For continuous initial loops one may first approximate
in the sphere bundle, preserving the loop class, and
smooth the extension away from a nonvanishing boundary
collar. Equivalently the relative Euler obstruction
itself gives the same product formula. \(\square\)

By naturality of the exact sequences, (5.1) induces
multiplication by \(\pm1\) on the quotients
\(\mathbb Z/d\). In particular it is an isomorphism
and takes every generator to a generator.

## 6. The simple inductive limit

For \(i\ge0\), put
\[
r_i=d2^i,\qquad
X_i=X_0\times\prod_{j<i}\mathbb{CP}^{r_j},
\qquad
E_i=\mathbf1^d\oplus
\bigoplus_{j<i}L_{j+1}^{\oplus r_j},
\qquad
B_i=\Gamma(X_i,\operatorname{End}E_i).
\tag{6.1}
\]
Then \(\operatorname{rank}E_i=r_i\) and \(\dim X_i=2r_i\).
Choose \(x_i\in X_i\) whose projections have dense tails
in every earlier base. For example, list each member
of a countable dense set in the infinite product
infinitely often and project its \(i\)-th member to
\(X_i\).

After fixing a fiber identification
\(E_i(x_i)\cong\mathbb C^{r_i}\), the decomposition
\[
E_{i+1}\cong\pi_i^*E_i\oplus(E_i(x_i)\otimes L_{i+1})
\]
defines unital injective *-homomorphisms
\[
\varphi_i:B_i\to B_{i+1},\qquad
\varphi_i(a)=\pi_i^*a\oplus
\bigl(a(x_i)\otimes1_{L_{i+1}}\bigr).
\tag{6.2}
\]
The coordinate block proves injectivity. Set
\[
A_d=\varinjlim(B_i,\varphi_i).
\]

For every fixed unitary \(g\in U(B_i)\), its evaluation
matrix \(g(x_i)\in U(r_i)\) can be joined to the identity
by a matrix-unitary path. Tensor that path with the new
line bundle and leave the coordinate block fixed.
Thus \(\varphi_i(g)\) is homotopic to
\(\pi_i^*g\oplus1_{L_{i+1}^{\oplus r_i}}\).
This is an assertion for each fixed unitary; it does
not presume a continuous global contraction of \(U(r_i)\).

Section 5 consequently shows that every map (6.2)
induces an isomorphism
\[
\pi_0U(B_i)\cong\mathbb Z/d
\longrightarrow
\pi_0U(B_{i+1})\cong\mathbb Z/d.
\tag{6.3}
\]
The image of (4.1) is a generator at every stage.

The standard structural argument for the preceding
twisted towers applies here, and we record its details.
A nonzero positive section at stage \(k\) is nonzero
on a nonempty open set. A later evaluation point
projects into that set, so the next evaluation block
is nonzero at every fiber. Its image is then full in
that homogeneous stage. If \(J\) is a nonzero ideal
of the limit, approximate a norm-one element of \(J_+\)
by a positive stage element \(a\) within \(1/8\).
The nonzero cutdown \((a-1/4)_+\) belongs to \(J\),
as seen in the quotient by \(J\). Its later fullness
puts the unit in \(J\). Hence \(A_d\) is simple.

The building blocks and injective countable system
make \(A_d\) separable, unital, nuclear, AH, and
infinite-dimensional. Every \(X_i\) has only even
cells; Morita equivalence and \(K\)-theory continuity
give \(K_1(A_d)=0\). The nonempty compact tracial state
spaces of the stages have a compatible family by
the finite intersection property: a finite set of
compatibility requirements is met by a trace at its
latest stage and backward restriction. The resulting
trace is faithful by simplicity. Its faithful matrix
amplifications give stable finiteness.

Finally, the component group of this unital injective
limit is the direct limit of the groups in (6.3).
Surjectivity follows by approximating any limit
unitary within \(1/100\) by a stage element and
taking its polar unitary, which is within \(2/100\)
of the original and hence homotopic to it.
For injectivity, partition a proposed null-homotopy
into steps of size below \(1/4\), approximate the
vertices within \(1/100\) in one common stage,
keeping the endpoints exact, and take polar unitaries.
Adjacent vertices are at distance below
\(1/4+4/100<2\) and can be joined in that stage by
principal logarithms. Thus a limit null-homotopy
would already occur at a finite stage.

It follows that
\[
U(A_d)/U_0(A_d)
\cong\varinjlim(\mathbb Z/d,\text{isomorphisms})
\cong\mathbb Z/d.
\]
The image of \(v_0\) generates this group. Its first
matrix stabilization contracts by the initial
contraction noted in Section 4. This proves the
theorem. \(\square\)

## References and dependencies

- [Exact factorial component groups](stw59-exact-factorial-component-groups-2026-09-05.md),
  Sections 2–4, for the dimension-dependent gauge/section
  fibration calculation, stable gauge identification, and
  integral relative-Euler normalization.
- A. Hatcher, *Vector Bundles and K-Theory*, §1.2, §2.3,
  §3.3, Proposition 3.13, and Proposition 4.3, for clutching,
  projective-space \(K\)-theory, relative obstruction theory,
  Euler/top-Chern identification, and Bott normalization.
  [Author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).
- C. Schochet, *Topological methods for C*-algebras II:
  Geometric resolutions and the Künneth formula*,
  Pacific J. Math. 98 (1982), 443–458, Künneth Theorem.
  [Publisher's paper](https://msp.org/pjm/1982/98-2/pjm-v98-n2-p15-s.pdf).
- R. Bott, *The stable homotopy of the classical groups*,
  Ann. of Math. 70 (1959), 313–337, especially the unstable
  group \(\pi_{2d}(U(d))=\mathbb Z/d!\).
  [Original paper](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bott4.pdf).
