# K-stability of tracial selfless C*-algebras by free spectral smoothing

Date: 5 September 2026. Complete proof; internal mathematical review
completed. No external peer review, formal verification, or publication
priority is claimed. This establishes the tracial selfless subclass of
LVIII; it does not settle LVIII for arbitrary pure C*-algebras.

The coordinating review checked Robert's precise hypotheses and unique
normalized 2-quasitrace conclusion, the free atom formula including the
zero-moment and scalar cases, the based smoothing homotopy, and the
finite-data reflection bounds, simplex interpolation, and boundary collar.

## 1. The theorem

A C*-probability space \((B,\tau)\) is **selfless** if \(B\ne\mathbb C\),
\(\tau\) induces a faithful GNS representation, and the first-factor
embedding into its reduced free product with itself is existential.
For the theorem below \(\tau\) is tracial, and is necessarily faithful.

**Theorem 1.** Let \((B,\tau)\) be a tracial selfless C*-probability
space. Then \(B\) is K-stable. More precisely, for all \(m\ge1\) and
\(k\ge0\), the canonical stabilization maps induce isomorphisms
\[
 \pi_k\bigl(U(M_m(B)),1\bigr)
 \xrightarrow{\ \cong\ }K_{k+1}(B).
 \tag{1}
\]
For \(k=0\), the source means unitary path components and the target
is \(K_1(B)\). In particular all consecutive corner-stabilization maps
are isomorphisms on every homotopy group.

No nuclearity, exactness, real rank zero, or separability is assumed.

The new ingredient is injectivity in positive degrees. The argument
first constructs a based homotopy in a free extension, then contracts
the smoothed family there using the reviewed small-support theorem,
and finally reflects the contraction back using existentiality.
It does not identify the original family merely by its stable K-class.

## 2. Exact primary-source inputs

We use the following structural facts.

1. [Leonel Robert, *Selfless C*-algebras*,
   arXiv:2309.14188](https://arxiv.org/pdf/2309.14188),
   published in *Advances in Mathematics* 478 (2025), 110409,
   [DOI](https://doi.org/10.1016/j.aim.2025.110409):
   Theorem 2.6(iv) says the inclusion
   \[
    (B,\tau)\longrightarrow
    (B,\tau)*(C(\mathbb T),m_{\mathbb T})
    \tag{2}
   \]
   is existential. Theorem 4.2 makes this reduced free product
   selfless. Theorem 3.1(ii) gives simplicity, stable rank one,
   and a unique normalized 2-quasitrace, equal to the specified
   trace, in the tracial case. Theorem 4.3 gives selflessness of
   \((M_m(B),\tau\otimes\operatorname{tr}_m)\).
   These are Theorems 2.6, 3.1, 4.2, and 4.3 on manuscript
   pp. 10, 13--14, 14--15, and 15--16, respectively.
2. [Miles Gould, *The Selfless Dichotomy*,
   arXiv:2606.09654v2](https://arxiv.org/pdf/2606.09654v2),
   Corollary 3, manuscript p. 2: every selfless C*-algebra is pure.
3. [Serban T. Belinschi, Hari Bercovici, and Ching-Wei Ho,
   *Regularity for free multiplicative convolution on the unit circle*,
   arXiv:2205.07114](https://arxiv.org/pdf/2205.07114),
   Lemma 3.1(1), manuscript p. 3; published in *Pacific Journal of
   Mathematics* 322 (2023), 243--250,
   [DOI](https://doi.org/10.2140/pjm.2023.322.243):
   if neither probability measure is a point mass, an atom of
   their free multiplicative convolution requires atoms of the
   two factors whose masses sum to more than one.
   In particular convolution with an atomless factor is atomless.
   A point-mass first factor is handled separately by rotation.
4. The internally reviewed
   [fixed spectral-point localization theorem](stw58-fixed-spectral-point-global-localization-2026-09-05.md)
   and
   [uniform small-support contraction theorem](stw58-small-quasitrace-support-kernel-contraction-2026-09-05.md)
   apply to simple unital finite pure coefficients with nonempty
   normalized quasitrace space.
5. The internally reviewed
   [all-degree stable-surjectivity theorem](stw58-compatible-split-stable-surjectivity-2026-09-05.md)
   supplies surjectivity in positive degrees for such coefficients.
   Its proof uses full hereditary endpoint matrix pieces and the
   degree-zero Rieffel stable range. For degree zero, stable rank
   one gives the usual \(K_1\)-bijectivity.

The freeness input in item 3 is a theorem about scalar spectral
distributions in a tracial free product. We use it only after item 1
has identified **every** normalized 2-quasitrace on the extension
with the free product trace.

A targeted primary-literature search on 5 September 2026 found the
structural results above, but did not locate a statement that all
tracial selfless C*-algebras are K-stable. This search is not evidence
of publication priority.

## 3. A free exponential gives an actual based smoothing homotopy

Set
\[
 (D,\rho)=(B,\tau)*(C(\mathbb T),m_{\mathbb T}),
\]
and identify \(B\) with its first-factor copy. Let \(w\) be the
canonical Haar unitary in the second factor, and set
\[
 a=\frac{1+\operatorname{Re}w}{2}.
 \tag{3}
\]
Then \(a\) is a positive contraction, is free from \(B\), and has
an atomless distribution on \([0,1]\): it is the pushforward of
Haar measure by \((1+\cos\theta)/2\). Each level set of this scalar
function is finite, so has Haar measure zero.

**Lemma 2.** For every based family \(u:S^k\to U(B)\), \(k\ge1\),
there is an explicit based homotopy in \(U(D)\) from \(u\) to a
family \(v\) whose spectral measure has no atom at \(-1\) at
any parameter point.

**Proof.** Fix a compatible metric on \(S^k\) and its basepoint
\(x_0\). Choose a continuous function
\[
 t:S^k\to[0,1],\qquad t^{-1}(0)=\{x_0\};
\]
normalized distance to \(x_0\) is one choice. Define
\[
 U_s(x)=u(x)\exp\bigl(i s\,t(x)a\bigr),
 \qquad 0\le s\le1,\qquad v(x)=U_1(x).
 \tag{4}
\]
This is norm-continuous in both variables. Since \(u(x_0)=1\)
and \(t(x_0)=0\), it is based throughout.

For \(x\ne x_0\), the function
\(r\mapsto e^{it(x)r}\) is injective on \([0,1]\), because
\(0<t(x)\le1<2\pi\). Hence \(\exp(it(x)a)\) has an atomless
spectral distribution. This unitary belongs to the second free
factor and is free from \(u(x)\).

The distribution of \(v(x)\) is therefore the free multiplicative
convolution of the distribution of \(u(x)\) and an atomless
measure. If the first distribution is not a point mass,
Belinschi--Bercovici--Ho Lemma 3.1(1) shows the product has no
atoms. If the first distribution is a point mass, the convolution
is a rotation of the atomless second measure, and again has no atoms.
Equivalently, faithfulness of the trace makes a unitary with a
point-mass distribution scalar, so this special case is immediate.

At the basepoint \(v(x_0)=1\), whose spectral measure is
\(\delta_1\). It has no atom at \(-1\). Thus the claimed atom
vanishes everywhere. \(\square\)

The factor in (4) is homotopic to one by its displayed exponential
path. There is no multiplication by a noncontractible Haar
unitary, and no basepoint correction which cancels the smoothing.

## 4. Contraction in the free extension

By the structural inputs, \(D\) is simple, unital, finite, and
pure, and
\[
 QT_1(D)=\{\rho\}.
 \tag{5}
\]
Finiteness follows from its faithful trace. Let \(u:S^k\to U(B)\)
be based and have zero stable class. Its first-factor image has
zero stable class in \(D\), and the homotopy (4) preserves this
class.

For the smoothed family \(v\), Lemma 2 gives
\[
 \mu_{x,\rho}(\{-1\})=0<1/(k+1)
 \qquad(x\in S^k).
\]
The fixed spectral-point theorem applies with \(\lambda=-1\).
It gives a based homotopy from \(v\) to a family supported in
uniform quasitrace dimension strictly less than \(1/(k+1)\).
The small-support theorem contracts that family. Consequently
the original image of \(u\) contracts in \(U(D)\).

The uniform arc used here exists even though \(t(x)\to0\) at the
basepoint. Indeed, the measures depend weakly continuously on
\(x\), the fixed point \(-1\) has zero mass everywhere, and the
compactness argument in the fixed-point theorem converts this
to one uniform arc bound. Uniform atomlessness at the basepoint
is neither true nor needed.

It remains to transfer this **actual contraction** back to \(B\).
That step uses the following elementary consequence of existentiality.

## 5. Existential embeddings reflect unitary nullhomotopies

**Lemma 3.** Let \(\iota:E\to F\) be an existential unital
embedding of C*-algebras, or of C*-probability spaces. Then
\[
 \pi_kU(E)\longrightarrow\pi_kU(F)
\]
is injective for every \(k\ge0\).

Only finitely many norm conditions are required to reflect a
given nullhomotopy. No existentiality assertion about an entire
function algebra is assumed.

**Proof.** Let \(u:S^k\to U(E)\) be a based family whose image
extends to a continuous map
\[
 H:D^{k+1}\to U(F),\qquad H|_{S^k}=\iota\circ u.
 \tag{6}
\]
For \(k=0\), interpret this as a path with its two prescribed
endpoints. Choose a finite triangulation of the disk, including
its boundary as a subcomplex, sufficiently fine that
\[
 \|H(y)-H(z)\|<1/100
 \quad\text{whenever }y,z\text{ belong to the same simplex}.
 \tag{7}
\]
The sphere basepoint may be chosen as a boundary vertex.

For every vertex \(p\), let \(z_p=H(p)\). Boundary vertices have
the fixed values \(z_p=\iota(u(p))\). Regard only the interior
vertex values as variables, all in the norm unit ball.
For each interior vertex impose the approximate unitary
conditions
\[
 \|z_p^*z_p-1\|<\varepsilon,\qquad
 \|z_pz_p^*-1\|<\varepsilon,
\]
and for every edge \((p,q)\) impose
\[
 \|z_p-z_q\|<1/100+\varepsilon,
 \tag{8}
\]
where \(\varepsilon=1/1000\). These requirements can be encoded
by the maximum of finitely many norms and positive parts of
norm differences; the boundary values are parameters from \(E\).
The corresponding infimum is zero in \(F\), using (7) and the
exact vertex unitaries. Existentiality therefore supplies
interior contractions \(y_p\in E\) satisfying these inequalities.
Set \(y_p=u(p)\) at boundary vertices.

Both approximate unitary conditions imply that \(y_p\) is
invertible. Its polar unitary \(v_p\in U(E)\) satisfies
\[
 \|v_p-y_p\|<2\varepsilon.
\]
For example, the spectrum of \(y_p^*y_p\) lies in
\((1-\varepsilon,1+\varepsilon)\), and the polar correction is
bounded by the maximal deviation of the singular values from
one. Boundary vertices are unchanged by this correction.
For every edge,
\[
 \|v_p-v_q\|<1/100+5\varepsilon<1/50.
 \tag{9}
\]
Every pair of vertices of a simplex forms an edge, so (9)
controls all vertex pairs of each simplex.

On each simplex with barycentric coordinates \(\lambda_p\),
form
\[
 A(y)=\sum_p\lambda_p(y)v_p.
\]
It lies within \(1/50\) of any one vertex unitary and is
therefore invertible. Its polar unitary
\[
 V(y)=A(y)(A(y)^*A(y))^{-1/2}
 \tag{10}
\]
gives a continuous \(U(E)\)-valued disk map. The formulas agree
on common faces because the barycentric formulas do.

On a boundary simplex all vertex values are the exact values
\(u(p)\). By (7),
\[
 \|A(x)-u(x)\|<1/100
 \quad(x\in S^k).
\]
Polar correction consequently gives
\[
 \|V(x)-u(x)\|<1/50.
 \tag{11}
\]
The polar part of the straight-line path between \(u(x)\) and
\(V(x)\) is a continuous unitary boundary homotopy. Attach this
homotopy as an outer collar to the disk (10), restoring the
prescribed boundary \(u\) exactly. This constructs a disk
extension of \(u\) in \(U(E)\).

Finally a disk extension yields an unbased contraction; if
\(K(x,s)\) is that contraction, replace it by
\[
 K(x,s)K(x_0,s)^*.
\]
Its initial value is \(u\), its final value is one, and it is
based throughout. Thus the based class vanishes.

For a homomorphism of C*-probability spaces, the same proof
uses only norm formulas, which are included in the expanded
language. It therefore applies unchanged. \(\square\)

The definition of existentiality used here is Robert's
Definition 1.1, manuscript p. 3. Its equivalent ultrapower
formulation appears immediately afterward on p. 4. The proof
above keeps the finite approximation, boundary restoration,
and norm bounds explicit instead of assuming that arbitrary
continuous parameter families lift coordinatewise from an
ultrapower.

## 6. Proof of K-stability

Let \(k\ge1\). Section 4 shows that every element in the kernel
of
\[
 \pi_kU(B)\longrightarrow K_{k+1}(B)
\]
becomes null in \(U(D)\). The inclusion \(B\to D\) is
existential by Robert's Theorem 2.6(iv). Lemma 3 therefore makes
the original element null in \(U(B)\). This proves injectivity.

Surjectivity follows from the reviewed all-degree stable-surjectivity
theorem because \(B\) is simple unital finite pure. Alternatively,
its full hereditary matrix-piece proof directly supplies each
stable class. For \(k=0\), stable rank one gives the canonical
bijection of components with \(K_1(B)\).

For every \(m\ge1\), Robert's Theorem 4.3 makes
\((M_m(B),\tau\otimes\operatorname{tr}_m)\) tracial selfless.
Repeat the argument for this coefficient algebra. It gives
all isomorphisms (1), with their canonical stable maps.

If \(j_m:U(M_m(B))\to U(M_{m+1}(B))\) is the corner inclusion,
the naturality identity
\[
 \sigma_{m+1}\,\pi_k(j_m)=\sigma_m
\]
now expresses \(\pi_k(j_m)\) as the composite of two
isomorphisms. This proves K-stability. \(\square\)

## 7. Scope and proof boundaries

The conclusion covers tracial selfless C*-algebras, including
nonnuclear examples furnished by the current selflessness
literature. It does not require such an example to absorb
\(\mathcal Z\).

The use of freeness has two distinct roles: it produces the
diffuse spectral distribution through the explicit homotopy
(4), and selflessness makes the inclusion existential so the
completed contraction can be reflected. Neither strict comparison
alone nor an embedding which merely preserves stable K-classes
supplies those roles.

The full LVIII question remains outside this theorem. The
argument needs the existential free extension, and it does not
derive that extension from pureness. The nontracial selfless
branch is purely infinite simple by the published/preprint
dichotomy and belongs to the classical purely infinite
K-stability theory; the proof established here is the tracial
branch, with its exact hypotheses stated in Theorem 1.
