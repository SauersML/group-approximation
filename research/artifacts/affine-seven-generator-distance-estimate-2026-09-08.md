# A seven-generator distance estimate for an affine integral group

Date: 2026-09-08.

Let

\[
B=\mathbb Z^3\rtimes\operatorname{SL}_3(\mathbb Z),\qquad
(v,A)(w,C)=(v+Aw,AC).
\]

Write \(\tau_v=(v,I)\), let \(e_1=(1,0,0)^t\), and set

\[
u_{ij}=(0,I+E_{ij})\quad(i\ne j),\qquad
S=\{u_{12},u_{13},u_{21},u_{23},u_{31},u_{32},\tau_{e_1}\}.
\]

**Theorem.** For every unitary representation \(\rho\) of \(B\) on a
complex Hilbert space \(H\), every \(\xi\in H\), and the orthogonal
projection \(P_B\) onto the vectors fixed by \(B\),

\[
\|\xi-P_B\xi\|
\leq C\max_{s\in S}\|\rho(s)\xi-\xi\|,
\qquad C=2+5\sqrt{3000}.                                      \tag{1}
\]

The same assertion holds for orthogonal representations on real Hilbert
spaces. No finite-dimensional hypothesis is made.

This proof uses the finite rational certificate specified below. All
subsequent steps are matrix identities, the spectral theorem, elementary
integral row operations, and Hilbert-space convexity. The deductions in this
note are written mathematical proofs; no additional Lean verification claim
is made.

## 1. The precise finite certificate and its matrix specialization

Let \(G_{13}\) be the group on the ordered generators

\[
a_{12},a_{13},a_{21},a_{23},a_{31},a_{32}
\]

with these thirteen relations, using \([a,b]=aba^{-1}b^{-1}\):

\[
\begin{aligned}
[a_{12},a_{23}]&=a_{13},& [a_{13},a_{32}]&=a_{12},\\
[a_{21},a_{13}]&=a_{23},& [a_{23},a_{31}]&=a_{21},\\
[a_{31},a_{12}]&=a_{32},& [a_{32},a_{21}]&=a_{31},             \tag{2}\\
[a_{12},a_{13}]&=1,& [a_{12},a_{32}]&=1,\\
[a_{13},a_{23}]&=1,& [a_{21},a_{23}]&=1,\\
[a_{21},a_{31}]&=1,& [a_{31},a_{32}]&=1,                    \tag{3}\\
(a_{12}a_{21}^{-1}a_{12})^4&=1.                            \tag{4}
\end{aligned}
\]

In the rational group ring of \(G_{13}\), let \(D\) be the column with
entries \(a_{ij}-1\), and let \(F\) be the \(13\times6\) Fox boundary
matrix of the displayed relators. The certificate consists of the identities
and bounds

\[
FD=0,\qquad
F^*F+DD^*=\frac1{250}I_6+Q^*Q+R,                            \tag{5}
\]

\[
\max_i\sum_j\|R_{ij}\|_{\ell^1}
\leq r_0,\qquad
\max_j\sum_i\|R_{ij}\|_{\ell^1}
\leq r_0,\qquad
r_0=\frac{11670886519714}{10^{16}}<\frac1{500}.             \tag{6}
\]

Here the involution in the group ring sends \(g\) to \(g^{-1}\) and fixes
rational coefficients. The entries of \(Q\) are specified by the exact
\(102\times6\times22\) integer coefficient table with denominator
\(10^8\) in
[LiteralP13HodgeData.lean](../../GroupApproximation/Sofic/LiteralP13HodgeData.lean).
The support reductions, residual coefficients, and identities are provided by
[LiteralP13HodgeReplay.lean](../../GroupApproximation/Sofic/LiteralP13HodgeReplay.lean),
[LiteralP13HodgeResidual.lean](../../GroupApproximation/Sofic/LiteralP13HodgeResidual.lean),
and the declarations `exactCertificate` and `cleanP13Certificate` in
[LiteralP13HodgeCertificate.lean](../../GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean).
Thus (5)--(6) refer to fixed finite rational data, not an existence assumption
about an unspecified certificate or a numerical approximation.

These identities can be evaluated in every unitary representation of
\(\operatorname{SL}_3(\mathbb Z)\). Indeed, the substitutions

\[
a_{ij}\longmapsto I+E_{ij}
\]

satisfy (2)--(3) by \(E_{ij}E_{kl}=\delta_{jk}E_{il}\). On coordinates
\(1,2\), the matrix \((I+E_{12})(I-E_{21})(I+E_{12})\) is
\(\begin{pmatrix}0&1\\-1&0\end{pmatrix}\), and it fixes coordinate
\(3\); this proves (4). Hence the universal property of the displayed
presentation gives a homomorphism
\(G_{13}\to\operatorname{SL}_3(\mathbb Z)\), through which any such
representation pulls back. No injectivity of this homomorphism is needed.

For completeness, the six matrices \(I+E_{ij}\) generate
\(\operatorname{SL}_3(\mathbb Z)\): their integral powers perform all
integer row additions. The Euclidean algorithm, with signed interchanges
\(\begin{pmatrix}0&1\\-1&0\end{pmatrix}\) also expressed as above,
reduces the first column of a unimodular matrix to \(e_1\). Its remaining
lower \(2\times2\) block has determinant one and is reduced in the same
way. Row additions then remove the remaining entries in the first row.
This reduces the original matrix to the identity using products of the six
matrices and their inverses.

## 2. The six-generator estimate on the linear subgroup

Let \(\sigma\) be any unitary representation of
\(\operatorname{SL}_3(\mathbb Z)\), and evaluate (5) in that
representation. Every group-ring entry has operator norm at most its
coefficient \(\ell^1\)-norm. The row and column estimates (6) give
\(\|R\|\leq r_0\) on \(H^6\). Explicitly, with
\(b_{ij}=\|R_{ij}\|_{\ell^1}\) and \(x_j=\|\eta_j\|\),

\[
\sum_i\Big(\sum_j b_{ij}x_j\Big)^2
\leq\sum_i\Big(\sum_j b_{ij}\Big)
                \Big(\sum_j b_{ij}x_j^2\Big)
\leq r_0^2\sum_jx_j^2.
\]

It follows that

\[
F^*F+DD^*\geq\frac1{500}I_{H^6}.                            \tag{7}
\]

Put

\[
A=D^*D
 =\sum_{i\ne j}(\sigma(I+E_{ij})-I)^*
                    (\sigma(I+E_{ij})-I).
\]

The operator \(A\) is positive and \(\|A\|\leq24\). Testing (7) on
\(D\xi\) and using \(FD=0\) gives

\[
\|A\xi\|^2\geq\frac1{500}\langle A\xi,\xi\rangle,
\qquad\text{that is,}\qquad A^2\geq\frac1{500}A.             \tag{8}
\]

The continuous spectral mapping theorem applied to (8) yields

\[
\operatorname{spec}(A)\subseteq\{0\}\cup[1/500,24].          \tag{9}
\]

The kernel of \(A\) is the joint fixed space of the six matrices, hence
the full fixed space of the linear subgroup. If \(P_L\) is its orthogonal
projection, the spectral theorem therefore gives

\[
\begin{aligned}
\|\xi-P_L\xi\|^2
&\leq500\langle A\xi,\xi\rangle\\
&=500\sum_{i\ne j}\|\sigma(I+E_{ij})\xi-\xi\|^2\\
&\leq3000\max_{i\ne j}\|\sigma(I+E_{ij})\xi-\xi\|^2.       \tag{10}
\end{aligned}
\]

The real case follows from the same real operator identities, or from
complexifying the representation. Conversely a complex representation can
be viewed as a real orthogonal representation without changing any norm or
fixed space.

## 3. Two primitive vectors suffice for every translation

An integer column \(v\) is primitive if the greatest common divisor of its
coordinates is one. Every primitive column is \(Ae_1\) for some
\(A\in\operatorname{SL}_3(\mathbb Z)\): applying the Euclidean row
operations just described to that column gives a determinant-one integer
matrix \(M\) with \(Mv=e_1\), and then \(A=M^{-1}\) works.

Every \(v=(a,b,c)^t\in\mathbb Z^3\), including zero, is a sum of two
primitive columns:

\[
(a,b,c)^t=(a-1,b,1)^t+(1,0,c-1)^t.                          \tag{11}
\]

The first summand has last coordinate one, and the second has first
coordinate one, so both are primitive. Consequently every translation is a
product of two linear-subgroup conjugates of \(\tau_{e_1}\).

If \(p\) is fixed by the linear subgroup, conjugation invariance of the
norm gives, for every primitive \(v=Ae_1\),

\[
\|\rho(\tau_v)p-p\|
=\|\rho(A)(\rho(\tau_{e_1})p-p)\|
=\|\rho(\tau_{e_1})p-p\|.
\]

Using (11), the triangle inequality gives the uniform estimate

\[
\sup_{v\in\mathbb Z^3}\|\rho(\tau_v)p-p\|
\leq2\|\rho(\tau_{e_1})p-p\|.                              \tag{12}
\]

This also shows that the seven elements in \(S\) generate \(B\).

## 4. Proof of the affine distance estimate

Fix \(\rho,\xi\) as in the theorem and write

\[
\delta=\max_{s\in S}\|\rho(s)\xi-\xi\|,\qquad
p=P_L\xi,\qquad d=\|\xi-p\|.
\]

By (10), \(d\leq\sqrt{3000}\delta\). For the controlled translation,

\[
\|\rho(\tau_{e_1})p-p\|
\leq\|\rho(\tau_{e_1})\xi-\xi\|+2\|\xi-p\|
\leq\delta+2d.
\]

By (12), the entire translation orbit
\(\mathcal O=\{\rho(\tau_v)p:v\in\mathbb Z^3\}\) lies in the
closed ball of radius \(M=2\delta+4d\) about \(p\). Its closed convex
hull \(K\) lies in the same ball. A nonempty closed bounded convex set in
a Hilbert space has a unique vector of least norm. For this assertion,
existence follows from the parallelogram identity applied to a sequence
whose norms tend to the infimum, and uniqueness follows from the same
identity applied to two minimizers.

Let \(y\) be that vector in \(K\). Translations permute \(\mathcal O\).
Each linear element \(A\) also permutes it, since \(\rho(A)p=p\) and

\[
\rho(A)\rho(\tau_v)p=\rho(\tau_{Av})p.
\]

Thus \(K\) is invariant under every element of \(B\). Those elements
act isometrically, so uniqueness of its least-norm vector implies that
\(y\) is fixed by all of \(B\). Also \(\|y-p\|\leq M\). Since
orthogonal projection minimizes distance to the closed fixed space,

\[
\begin{aligned}
\|\xi-P_B\xi\|
&\leq\|\xi-y\|\\
&\leq d+M=2\delta+5d\\
&\leq(2+5\sqrt{3000})\delta.
\end{aligned}
\]

This proves (1), including the case \(\delta=0\).

## 5. The fixed-space projection belongs to the represented C*-algebra

For the same seven elements set

\[
A_B=\sum_{s\in S}(\rho(s)-I)^*(\rho(s)-I),\qquad
\gamma=C^{-2}=(2+5\sqrt{3000})^{-2}.
\]

Then \(0\leq A_B\leq28I\), its kernel is the fixed space of \(B\), and
(1) gives

\[
\|\xi-P_B\xi\|^2
\leq C^2\max_{s\in S}\|\rho(s)\xi-\xi\|^2
\leq C^2\langle A_B\xi,\xi\rangle.
\]

Therefore

\[
A_B\geq\gamma(I-P_B),\qquad
\operatorname{spec}(A_B)\subseteq\{0\}\cup[\gamma,28].       \tag{13}
\]

In particular, with \(f(t)=\max\{1-t/\gamma,0\}\) on \([0,28]\),

\[
P_B=f(A_B)\in C^*(I,\rho(B)).                               \tag{14}
\]

The polynomial formula

\[
P_B=\lim_{m\to\infty}(I-A_B/28)^m                           \tag{15}
\]

holds in operator norm; the error is at most
\((1-\gamma/28)^m\).

The same conclusion holds intrinsically in any unital C*-algebra
\(\mathcal A\). If \(\pi:B\to\mathcal U(\mathcal A)\) is a
homomorphism, form

\[
a=\sum_{s\in S}(\pi(s)-1)^*(\pi(s)-1)\in\mathcal A.
\]

Represent \(\mathcal A\) faithfully and unitally on a Hilbert space.
Applying (13) there and using spectral permanence gives
\(\operatorname{spec}_{\mathcal A}(a)\subseteq\{0\}\cup[\gamma,28]\).
Hence \(p=f(a)\) is a projection in \(\mathcal A\). In every unital
Hilbert-space representation of \(\mathcal A\), its image is exactly the orthogonal
projection onto the vectors fixed by the induced representation of \(B\).
Indeed functional calculus is preserved by representations, and the same
kernel and gap argument applies after each representation. In particular,

\[
\pi(b)p=p=p\pi(b)\qquad(b\in B).                            \tag{16}
\]

There is also the following purely algebraic characterization, useful when
\(\mathcal A\) is a matrix corona: if \(x\in\mathcal A\) satisfies
\(\pi(b)x=x\) for all \(b\in B\), then \(ax=0\), so the norm limit
(15) gives \(px=x\).

For example, suppose \(v\in\mathcal U(\mathcal A)\) satisfies
\(v\pi(B)v^*\subseteq\pi(B)\). Equation (16) then implies
\(\pi(b)v^*p=v^*p\) for every \(b\in B\). The characterization just
proved gives \(pv^*p=v^*p\), whence

\[
p\leq vpv^*.                                                \tag{17}
\]

If every projection of \(\mathcal A\) is finite, (17) is an equality:
\(p\) and \(vpv^*\) are unitarily equivalent, and a finite projection
cannot be equivalent to a proper subprojection of itself. This last step is
an additional finiteness assumption on \(\mathcal A\); (1)--(16) require
none.
