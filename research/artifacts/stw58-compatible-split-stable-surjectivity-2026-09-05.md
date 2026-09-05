# STW LVIII: compatible split surjectivity onto stable K-theory

Date: 2026-09-05. **Complete proof, internally reviewed.**
The root review checked the compact-unit finite-matrix bridge, the
nonzero endpoint and multiplier matrix units, the nonunital stable
range, coherent group sections, and the finite-coordinate field proof.
No external peer review, formal verification, or novelty priority is claimed.
This proves the stable-surjectivity half of K-stability in the unital simple
finite pure case; it does not prove STW LVIII.

## 1. Statement and conventions

A C*-algebra is **pure** when its Cuntz semigroup is almost unperforated
and almost divisible. For a unital algebra, **finite** means that its
unit is a finite projection. All homotopy groups below use the norm
topology and the identity as basepoint. Write
\[
G_m^k(B)=\pi_k(U(M_m(B)),1_m),\qquad
K=K_{k+1}(B),
\]
where the K-theory subscript is read modulo two. Let
\[
t_m:G_m^k(B)\longrightarrow G_{m+1}^k(B)
\]
be induced by \(u\mapsto\operatorname{diag}(u,1_B)\), and let
\(\sigma_m:G_m^k(B)\to K\) be stabilization followed by Bott periodicity.

**Theorem 1.** Let \(B\) be a nonzero unital simple finite pure C*-algebra.
For each fixed integer \(k\ge1\), there are group homomorphisms
\[
s_m:K\longrightarrow G_m^k(B)\quad(m\ge1)
\]
such that
\[
\sigma_m s_m=\operatorname{id}_K,\qquad
t_m s_m=s_{m+1}.                                      \tag{1}
\]
Consequently, putting \(N_m=\ker\sigma_m\), there are compatible
isomorphisms of abelian groups
\[
G_m^k(B)\cong K\oplus N_m,\qquad
t_m=\operatorname{id}_K\oplus(t_m|_{N_m}),\qquad
\varinjlim_m N_m=0.                                   \tag{2}
\]

The sections are sections of homotopy **groups**, not asserted to arise
from continuous sections of unitary spaces. The choice may depend on
\(k\), and need not be canonical. No separability, nuclearity, exactness,
or trace hypothesis is added.

In degree zero, the canonical component map is already bijective by
stable rank one and the usual nonstable \(K_1\) theorem. The new deduction
here concerns every positive degree and compatibility in the matrix size.

More generally, the proof works for any unital simple stable-rank-one
algebra whose unit has the divisibility inequalities used in Section 2.

## 2. Producing a full hereditary matrix piece

By Lin's pure-algebra dichotomy, a simple pure algebra is either purely
infinite or has stable rank one. Finiteness excludes the former case,
so \(\operatorname{sr}(B)=1\). Unitality supplies \(\sigma\)-unitality;
no separability is needed for this application. This is published
prior art: [Lin, Theorem 3.6](https://doi.org/10.1016/j.jfa.2025.111065).

Fix \(k\ge1\) and choose \(N\ge k+2\). Almost divisibility, applied to the
compact class of the unit, gives
\[
Nx\le[1_B]\le(N+1)x\quad\text{for some }x\in\mathrm{Cu}(B). \tag{3}
\]
This also follows from the formulation of almost divisibility using a
pair \(a'\ll a\), by taking both equal to the compact unit class.

The distinction between \(\mathrm{Cu}(B)\) and the finite-matrix Cuntz
semigroup \(W(B)\) matters. Write \(x=\sup_jx_j\), where \(x_j\in W(B)\)
increase and satisfy \(x_j\le x\). Such an approximation follows by
finite-matrix approximation and positive cutoffs in \(B\otimes\mathcal K\).
Compactness of \([1_B]\) and preservation of increasing suprema by
addition give an index \(j\) with
\[
Nx_j\le[1_B]\le(N+1)x_j.                               \tag{4}
\]
The inclusion \(W(B)\subset\mathrm{Cu}(B)\) reflects order, so these
are inequalities in \(W(B)\).

Rørdam--Winter's Proposition 5.1 applies precisely to a unital
stable-rank-one algebra satisfying (4), and provides a unital
homomorphism
\[
\theta:Z_{N,N+1}\longrightarrow B.                     \tag{5}
\]
See [the author manuscript, Proposition 5.1, printed p. 9](https://web.math.ku.dk/~rordam/manus/jiang-su-revisited.pdf)
and [arXiv:0801.2259v1](https://arxiv.org/pdf/0801.2259v1).
The required map is a homomorphism; its injectivity, compatibility
with maps for other \(N\), or approximate centrality is not required.

Concretely,
\[
Z_{N,N+1}=
\{f\in C([0,1],M_N\otimes M_{N+1}):
 f(0)\in M_N\otimes1,\ f(1)\in1\otimes M_{N+1}\}.
\]
Its canonical order-zero maps are
\[
a\longmapsto[t\mapsto(1-t)(a\otimes1)],\qquad
b\longmapsto[t\mapsto t(1\otimes b)].
\]
Compose with \(\theta\), obtaining \(\phi_i:M_{N+i}\to B\), \(i=0,1\).
Set \(h_i=\phi_i(1)\). Then \(h_0+h_1=1_B\), so at least one
\(h_i\) is nonzero. Choose such an \(i\), and set
\[
n=N+i,\qquad C=\operatorname{Her}_B(h_i).
\]
Simplicity makes \(C\) full in \(B\).

We record why this hereditary algebra has actual matrix coefficients,
rather than merely a matrix-shaped Cuntz class. The supporting
homomorphism \(\pi:M_n\to B^{**}\) of \(\phi_i\) has unit equal to the
support \(q\) of \(h_i\) and commutes with \(h_i\). Order-zero functional
calculus gives
\(\pi(e_{ab})h_i^{1/2}\in B\). Thus multiplication on either side by
\(\pi(e_{ab})\) preserves the closure of
\(h_i^{1/2}Bh_i^{1/2}\), namely \(C\). Therefore
\[
\pi:M_n\longrightarrow M(C)
\]
is a unital homomorphism into its multiplier algebra. For
\(D=\pi(e_{11})C\pi(e_{11})\), the usual matrix-unit formulas give
\[
C\cong M_n(D).                                        \tag{6}
\]
The corner \(D\) is hereditary in \(C\), and hence in \(B\).
Stable rank one passes to hereditary subalgebras, so
\(\operatorname{sr}(D)=1\).

Only one nonzero endpoint piece was used. The second piece and their
overlap may be zero. No fragmentation or homotopy-pushout assertion
enters the argument.

## 3. The matrix-piece stable range, including nonunital coefficients

For a possibly nonunital C*-algebra \(A\), let \(U_m(A)\) mean the
unitaries in \(1_m+M_m(A)\); when \(A\) is unital, use the ordinary
unitary group of \(M_m(A)\). For \(C\subset B\) these groups embed
as supported unitaries in \(U(M_m(B))\): in the unital-corner case
with unit \(p\), the map is \(u\mapsto u+(1_B-p)1_m\).

**Lemma 2.** If \(\operatorname{sr}(D)=1\), \(k\ge1\), and \(r\ge k+2\),
then canonical stabilization is an isomorphism
\[
\pi_k U_r(D)\ \xrightarrow{\ \cong\ }\ K_{k+1}(D).       \tag{7}
\]

**Proof.** First suppose \(D\) unital. Embed \(S^k\) as a closed subset
of a coordinate chart in \(\mathbb T^{k+1}\). The stable-rank estimate
for crossed products by \(\mathbb Z\), applied successively to trivial
actions, and the quotient estimate yield
\[
\operatorname{sr}C(S^k,D)
 \le\operatorname{sr}C(\mathbb T^{k+1},D)
 \le\operatorname{sr}(D)+k+1=k+2.                       \tag{8}
\]
The restriction to the sphere is surjective: continuous Banach-space
valued functions extend from a closed subset of a compact metric space,
or equivalently one uses the exact tensor product with the commutative
restriction sequence.

Rieffel's degree-zero stabilization theorem identifies
\(\pi_0 U(M_r(A))\) with \(K_1(A)\) whenever \(r\ge\operatorname{sr}(A)\).
Apply it to \(A=C(S^k,D)\) and \(A=D\). Evaluation at the sphere
basepoint splits their unitary map spaces, explicitly by
\[
f\longmapsto\bigl(f(x_0),\,x\mapsto f(x_0)^*f(x)\bigr).
\]
On path components its kernel is the based homotopy group
\(\pi_k U_r(D)\). The stable kernel is
\(K_1(C_0(S^k\setminus\{x_0\})\otimes D)=K_{k+1}(D)\).
Naturality of evaluation and its constant section now prove (7).

For nonunital \(D\), let \(\widetilde D\) be its minimal unitization.
It has stable rank one, so the preceding argument applies to it.
The scalar quotient \(q:U(M_r(\widetilde D))\to U(r)\) has the scalar
section \(j\), and
\[
g\longmapsto\bigl(gj(q(g))^*,q(g)\bigr)                 \tag{9}
\]
is a homeomorphism onto \(U_r(D)\times U(r)\).
The induced split homotopy sequence is natural under stabilization.
The scalar group is in its usual stable range in degree \(k\), since
\(k<2r\). Taking kernels in the two split stabilization sequences
therefore proves (7) for \(D\). For \(k=1\) these are still abelian
groups, as is true for the fundamental group of every topological
group. \(\square\)

The prior-art inputs in this proof are stable-rank estimates, degree-zero
stabilization, and Bott periodicity. In particular, it does **not**
use an inference from Rieffel's all-torus Theorem 3.3 to general
degree-one injectivity at matrix size one. The local derivation is the
matrix-piece lemma already recorded in
[the soft-module note](../../notes/stw58-soft-module-compression-attempt-2026-09-05.md)
and [the reviewed local-factorization artifact, Section 4](stw58-local-factorization-and-overlap-cancellation-2026-09-05.md).
For the precise low-degree citation boundary, see
[the primary-source audit](stw58-degree-one-primary-citation-audit-2026-09-05.md).

## 4. Coherent sections from one fixed hereditary piece

Retain the single algebra \(C\cong M_n(D)\) selected in Section 2.
For every \(m\ge1\), we have \(mn\ge k+2\). Lemma 2 and (6)
therefore identify
\[
\pi_k U_m(C)\cong K_{k+1}(C).
\]
The identification is the canonical stabilization map. Full hereditary
inclusion induces the canonical Morita-invariance isomorphism
\(K_{k+1}(C)\to K_{k+1}(B)=K\). Denote the composite isomorphism by
\[
\alpha_m:\pi_k U_m(C)\xrightarrow{\ \cong\ }K.          \tag{10}
\]
Let
\[
j_m:\pi_k U_m(C)\longrightarrow G_m^k(B)
\]
be supported inclusion. Its naturality with stabilization gives
\[
\sigma_mj_m=\alpha_m.                                 \tag{11}
\]
Define
\[
s_m=j_m\alpha_m^{-1}.                                 \tag{12}
\]
Then (11) gives \(\sigma_ms_m=\operatorname{id}_K\).

Let \(a_m:\pi_kU_m(C)\to\pi_kU_{m+1}(C)\) denote corner
stabilization. The same naturality gives
\[
\alpha_{m+1}a_m=\alpha_m,\qquad
t_mj_m=j_{m+1}a_m.
\]
Consequently,
\[
t_ms_m
 =j_{m+1}a_m\alpha_m^{-1}
 =j_{m+1}\alpha_{m+1}^{-1}
 =s_{m+1},                                           \tag{13}
\]
which proves (1). This uses the same \(C\) for all \(m\) in this
fixed degree; independently choosing a new endpoint piece at each
matrix size would not automatically give (13).

Since the groups \(G_m^k(B)\) are abelian, the explicit splitting is
\[
x\longmapsto\bigl(\sigma_mx,\ x-s_m(\sigma_mx)\bigr),
\quad
(a,z)\longmapsto s_m(a)+z.                             \tag{14}
\]
Equation (13) proves the asserted form of the transition maps in (2).

Finally, stable K-theory is the direct limit of these homotopy groups.
In particular, if \(z\in N_m\), its stable class is zero and there
is some \(\ell\ge m\) for which its image in \(G_\ell^k(B)\) is zero.
This is the usual finite-matrix detection of a compact based
nullhomotopy. One can obtain it by uniformly approximating a stable
unitary homotopy over the compact parameter space
\(S^k\times[0,1]\) in a common finite matrix corner and applying polar
decomposition, with the already finite endpoints retained.
Thus every element of the kernel system eventually vanishes, proving
\(\varinjlim_mN_m=0\). This completes Theorem 1. \(\square\)

## 5. K1-surjectivity for all locally compact coefficient spaces

**Corollary 3.** For every locally compact Hausdorff space \(X\), every
class in \(K_1(C_0(X,B))\) is represented by a unitary in
\(1+C_0(X,B)\). For compact \(X\), equivalently the canonical map
\[
U(C(X,B))/U_0(C(X,B))\longrightarrow K_1(C(X,B))
\]
is surjective.

No purity or stable rank assertion about \(C_0(X,B)\) is made.

**Proof for compact \(X\).** Represent the given K-class by
\(u\in U(M_\ell(C(X,B)))\). Finite sums of continuous scalar functions
times elements of \(M_\ell(B)\) are dense in \(C(X,M_\ell(B))\).
Choose such a sum \(w\) with \(\|w-u\|<1/4\). Collect its finitely
many scalar coefficient functions into a continuous map
\[
q:X\longrightarrow Y\subset[0,1]^r,
\]
using real and imaginary parts and affine rescaling. By definition,
\(Y=q(X)\), so \(Y\) is compact metric and \(q\) is surjective.
There is \(w_Y\in M_\ell(C(Y,B))\) with \(q^*w_Y=w\).

The element \(w\) is invertible because it is within \(1/4\) of \(u\).
Surjectivity of \(q\) shows that every \(w_Y(y)\) is invertible.
Its inverse is continuous, so \(w_Y\) is invertible as an element
of \(M_\ell(C(Y,B))\). Put
\[
u_Y=w_Y(w_Y^*w_Y)^{-1/2}.
\]
The polar part of the straight-line invertible path from \(u\) to
\(w\) is a unitary homotopy from \(u\) to \(q^*u_Y\). Thus it suffices
to represent \([u_Y]\) by a size-one unitary over \(Y\).

Choose \(N\ge r+2\), and perform Section 2's construction for this
\(N\), obtaining a full \(C\cong M_n(D)\subset B\), where \(n\ge N\)
and \(\operatorname{sr}(D)=1\). The compact cube, and hence \(Y\),
embeds as a closed subset of a coordinate chart in \(\mathbb T^r\).
Consequently
\[
\operatorname{sr}C(Y,\widetilde D)\le r+1,\qquad
\operatorname{sr}C(Y)\le r+1.                          \tag{15}
\]
When \(D\) is unital, use \(D\) in place of \(\widetilde D\).
Rieffel's degree-zero theorem at size \(n\) now applies.

For completeness, in the nonunital case the extension
\[
0\to C(Y,D)\to C(Y,\widetilde D)\to C(Y)\to0
\]
has its scalar section. At matrix size \(n\), the analogue of (9)
splits its unitary space into the kernel and \(U(M_n(C(Y)))\).
Both the total and scalar component maps are isomorphisms onto
K-theory by (15). Taking their kernels therefore proves that every
class of
\[
K_1(C(Y,C))=K_1(M_n(C(Y,D)))
\]
is represented by a supported size-one unitary of \(C(Y,C)\).

The inclusion \(C(Y,C)\subset C(Y,B)\) is full hereditary. To see
fullness without a pointwise-to-global assumption, fullness of \(C\)
in the unital algebra \(B\) gives a finite sum from \(BCB\) sufficiently
close to \(1_B\); its constant section is then invertible in the ideal
generated by \(C(Y,C)\). Hence this ideal is all of \(C(Y,B)\).
Full hereditary K-theory invariance now supplies a preimage of
\([u_Y]\), represented by the supported unitary just constructed.
Its inclusion in \(U(C(Y,B))\), followed by pullback along \(q\),
represents the original class in \(K_1(C(X,B))\).

**Passage to locally compact \(X\).** Let \(X^+\) be its one-point
compactification and put \(J=C_0(X,B)\). The evaluation extension
\[
0\to J\to C(X^+,B)\xrightarrow{\operatorname{ev}_\infty}B\to0
\]
has the constant section, and hence induces an injection on \(K_1(J)\).
Given \(\xi\in K_1(J)\), the compact case supplies
\(u\in U(C(X^+,B))\) representing its image. Its value \(u(\infty)\)
has zero \(K_1(B)\)-class. Stable rank one gives a path from this
value to \(1_B\). Define
\[
v(x)=u(x)u(\infty)^*.
\]
Then \(v(\infty)=1_B\), so \(v\in1+J\), and multiplying by the
constant path shows that \(u\) and \(v\) have the same \(K_1\)-class
over \(X^+\). Injectivity of \(K_1(J)\to K_1(C(X^+,B))\) implies
that \(v\) represents \(\xi\). \(\square\)

Only surjectivity is asserted for arbitrary \(X\). The finite-coordinate
choice can depend on the K-class; it does not provide a coherent group
section for all classes over an arbitrary compact space.

## 6. What remains for LVIII

For this class of algebras, every stable K-class in every positive degree
already has a representative at matrix size one, and has the compatible
chosen representatives (12) at all matrix sizes.

A consecutive map \(t_m\) is surjective exactly when its restriction
\(N_m\to N_{m+1}\) is surjective. Nothing above establishes that.
Likewise, no \(N_m\) has been shown to vanish. The assertion
\(\varinjlim N_m=0\) means elementwise eventual vanishing; it gives no
uniform stabilization bound.

Thus K-stability in the present simple finite slice reduces to proving
that the canonical stabilization maps have zero kernel in every degree
and matrix size. Proving zero kernels for every algebra in this class
at size one would suffice, since the class is closed under matrix
amplification. This is a reduction of the remaining work, not a
solution of that injectivity problem or of general STW LVIII.

## 7. Sources and provenance

The ingredients are established prior art; the compatible splitting
argument is written out here as a deduction from them. No claim of
priority for this deduction is made.

- Huaxin Lin, *Strict comparison and stable rank one*, Journal of
  Functional Analysis 289 (2025), 111065, Theorem 3.6:
  [published source](https://doi.org/10.1016/j.jfa.2025.111065).
- Mikael Rørdam and Wilhelm Winter, *The Jiang–Su algebra revisited*,
  Journal für die reine und angewandte Mathematik 642 (2010), 129–155,
  Proposition 5.1 and the order-zero preliminaries:
  [author manuscript](https://web.math.ku.dk/~rordam/manus/jiang-su-revisited.pdf),
  [DOI](https://doi.org/10.1515/crelle.2010.039).
- Marc A. Rieffel, *Dimension and stable rank in the K-theory of
  C*-algebras*, Proceedings of the London Mathematical Society 46
  (1983), 301–333: hereditary permanence, quotient and crossed-product
  stable-rank estimates, and nonstable \(K_1\):
  [DOI](https://doi.org/10.1112/plms/s3-46.2.301).
- Marc A. Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*,
  Journal of Operator Theory 17 (1987), 237–254, Theorem 2.10,
  printed p. 243:
  [original scanned paper](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf).
  Theorem 2.10 is the degree-zero theorem used in Lemma 2.
- The compact-unit \(W\)-to-\(\mathrm{Cu}\) bridge and finite
  dimension-drop input were already checked in
  [the scalar unstable-homotopy audit](stw99-lxxvi-scalar-unstable-homotopy-audit-2026-09-05.md).
