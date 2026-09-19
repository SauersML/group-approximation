# STW LVIII: contraction of kernels with small varying projection support

Date: 2026-09-05. **Complete proof; internal mathematical review completed.**
No external peer review, formal verification, or novelty priority is claimed.
This is a kernel-vanishing theorem for explicitly localized families.
It does not provide localization of every family and does not solve LVIII.

## 1. Two concrete conclusions

Let \(X\) be a connected finite CW complex of dimension \(d\ge1\), let
\(B\) be a nonzero unital simple C*-algebra of stable rank one, and put
\(A=C(X,B)\). Let \(p\in A\) be a projection with \(p(x)\ne0\) for every
\(x\in X\). Say a unitary \(u\in U(A)\) is **supported by \(p\)** if
\[
u-1=p(u-1)p.
\tag{1}
\]

**Theorem 1 (orthogonal-copy criterion).** Suppose \(N\ge d+1\) and
\[
(N-1)[p]\le[1-p]\quad\text{in }\mathrm{Cu}(A).
\tag{2}
\]
If \(u\) satisfies (1) and its class in \(K_1(A)\) is zero, then
\(u\in U_0(A)\).

In particular, if \(X=S^k\), \(k\ge1\), and \(u\) is based at \(1_B\),
it has a based nullhomotopy. The projection \(p(x)\) is allowed to
vary over the whole sphere; no fixed hereditary subalgebra of \(B\)
is presumed to contain the family.

For this sphere formulation, stable nullness of
\([u]\in\pi_kU(B)\) is exactly zero of its reduced
\(K_1(C(S^k,B))\)-class. Indeed, evaluation at the basepoint has
the constant section and gives the split extension
\[
0\to C_0(S^k\setminus\{x_0\},B)\to C(S^k,B)\to B\to0.
\]
Its K1 kernel is the suspension group \(K_{k+1}(B)\), and
stabilization of a based sphere family is its canonical class
in this kernel. Since \(u(x_0)=1_B\), its constant component
is zero. Thus a zero stable \(\pi_k\)-class satisfies the
\([u]=0\) in \(K_1(A)\) hypothesis in Theorem 1.

**Theorem 2 (quantitative trace criterion).** Suppose additionally
that \(B\) is finite and pure, and that \(0<p(x)<1_B\) for every \(x\).
If
\[
\sup_{\substack{x\in X\\ \tau\in\mathrm{QT}_1(B)}}
       \tau(p(x))<\frac1{d+1},
\tag{3}
\]
then every stably null unitary satisfying (1) contracts in \(U(A)\).
Here \(\mathrm{QT}_1(B)\) denotes normalized bounded 2-quasitraces.
Equivalently, one may assume there is a constant \(c<1/(d+1)\)
with \(\tau(p(x))\le c\) for every such \(x,\tau\).

For a loop, (3) is the explicit bound \(c<1/2\); for a two-sphere,
it is \(c<1/3\). Neither theorem says that a general unstable kernel
class can be moved into such a support.

## 2. Stable rank of a varying projection corner

**Lemma 3.** Under the hypotheses of Theorem 1,
\[
\operatorname{sr}\bigl(pC(X,B)p\bigr)\le d+1.
\tag{4}
\]

**Proof.** Use a finite CW structure on \(X\), with \(X_j\) its
\(j\)-skeleton, and put
\[
D_j=p|_{X_j}\,C(X_j,B)\,p|_{X_j}.
\]
Each nonzero fiber corner \(p(x)Bp(x)\) has stable rank one by
hereditary permanence of stable rank one.

The projection bundle is trivial on each pulled-back closed
characteristic disk. Here is a direct check that requires no
triviality of the bundle over \(X\). If \(P:D^j\to B\) is the
pullback projection, consider \(P(tz)\), \(0\le t\le1\). By compactness
there is a common finite subdivision of \(t\) for which successive
projections have norm distance less than one, uniformly in \(z\).
The canonical polar unitary intertwining two close projections,
multiplied over the subdivision, is a continuous unitary conjugating
\(P(0)\) to \(P(z)\). Thus the corner bundle is trivial over this disk
and over its open cell.

Restriction therefore gives an extension
\[
0\longrightarrow
 \bigoplus_{\text{\(j\)-cells }e} C_0(\mathbb R^j,D_e)
 \longrightarrow D_j
 \longrightarrow D_{j-1}
 \longrightarrow0,
\tag{5}
\]
where every \(D_e\) is a nonzero unital corner of \(B\), of stable
rank one. Restriction is surjective: extend a \(B\)-valued section
from the closed skeleton by the Banach-valued extension theorem and
then compress by the globally given projection \(p\).

The algebra \(C_0(\mathbb R^j,D_e)\) is an ideal of
\(C(\mathbb T^j,D_e)\), using
\(\mathbb R^j\cong(\mathbb T\setminus\{1\})^j\).
Hereditary permanence of the stable-rank upper bound, and successive
trivial crossed products by \(\mathbb Z\), give
\[
\operatorname{sr}C_0(\mathbb R^j,D_e)
 \le\operatorname{sr}C(\mathbb T^j,D_e)\le j+1.
\tag{6}
\]
The standard extension inequality is
\[
\operatorname{sr}(E)\le
\max\{\operatorname{sr}(I),\operatorname{sr}(E/I)+1\}.
\tag{7}
\]
Starting with \(\operatorname{sr}(D_0)=1\), equations (5)--(7)
prove inductively that \(\operatorname{sr}(D_j)\le j+1\).
At \(j=d\) this is (4). \(\square\)

Only the ideal case of the stable-rank inequality is used in (6);
no monotonicity under arbitrary hereditary inclusions at higher
stable rank is being assumed. The estimates (6)--(7) are prior art,
recorded with the original Rieffel references in
[Blackadar, V.3.1.21--23, printed p. 474](https://www.bruceblackadar.com/Mathematics/Cycr.pdf).

## 3. Proof of the orthogonal-copy criterion

Because (2) compares projections, Cuntz subequivalence is implemented
by an actual rectangular partial isometry. There are
\(v_2,\ldots,v_N\in A\) with
\[
v_i^*v_i=p,\qquad
q_i=v_iv_i^*\le1-p,\qquad q_iq_j=0\quad(i\ne j).
\tag{8}
\]
This follows by applying the projection subequivalence fact to
\(\operatorname{diag}(p,\ldots,p)\) and \(1-p\), and taking the
columns of the resulting rectangular matrix.
Set \(v_1=p\), \(q_1=p\), and \(q=\sum_{i=1}^Nq_i\).
The matrix units \(v_iv_j^*\) identify
\[
qAq\cong M_N(D),\qquad D=pAp.
\tag{9}
\]
Explicitly, \((a_{ij})\) maps to \(\sum_{ij}v_ia_{ij}v_j^*\).
Under this identification the supported unitary \(u\) corresponds,
after restriction to \(q\), to
\[
\operatorname{diag}(pup,p,\ldots,p)\in U(M_N(D)).
\tag{10}
\]

The projection \(p\) is full in \(A\). Indeed, its image is nonzero
and therefore full in every simple fiber \(B\). For an elementary
global justification, on a neighborhood of each point one can
choose a finite positive sum
\(\sum a_jp a_j^*\) bounded below by a positive scalar.
A finite subcover and a subordinate central partition of unity
combine these sums into an invertible positive element of the
ideal generated by \(p\). Thus that ideal is all of \(A\).
The larger projection \(q\) is consequently full as well.

Full corner inclusion gives an isomorphism
\[
K_1(qAq)\longrightarrow K_1(A).
\tag{11}
\]
This is where simplicity and nonzero fibers of \(p\) are used;
stable nullness does not in general descend through an arbitrary
ideal inclusion. Equations (1), (10), and (11) imply that (10)
has zero stable K-class.

By Lemma 3, \(\operatorname{sr}(D)\le d+1\le N\).
Rieffel's degree-zero stabilization theorem, applied to \(D\)
at matrix size \(N\), says that
\[
U(M_N(D))/U_0(M_N(D))\longrightarrow K_1(D)
\]
is an isomorphism. Hence (10) contracts in \(U(M_N(D))\).
Use (9) and add \(1-q\) to this homotopy. It becomes a homotopy
from \(u\) to \(1\) in \(U(A)\), proving Theorem 1.

For a based sphere family, this initially gives a possibly unbased
homotopy \(H:S^k\times[0,1]\to U(B)\). Replace it by
\[
H_0(x,t)=H(x,t)H(x_0,t)^*.
\tag{12}
\]
Since both endpoints already have value \(1_B\) at \(x_0\),
this keeps the required endpoints and makes the homotopy based.
No assertion that (12) stays supported in the original varying
projection is needed.

## 4. From fiber trace size to actual copies

We first justify the quasitrace passage; it is not enough simply
to presume that an arbitrary quasitrace on a function algebra is
point evaluation.

**Lemma 4.** If \(p\in C(X,B)\) is a projection and
\(\tau(p(x))\le c\) for every \(x\) and
\(\tau\in\mathrm{QT}_1(B)\), then
\[
\rho(p)\le c
\quad\text{for every }\rho\in\mathrm{QT}_1(C(X,B)).
\tag{13}
\]

**Proof.** Choose a finite cover on each member of which \(p(x)\)
is continuously unitarily conjugate to a fixed projection
\(p_i=p(x_i)\) in \(B\), and a central partition of unity
\(f_i\) with supports inside these members. Choose the local
conjugating unitary \(w_i\) so that
\(w_ip_iw_i^*=p\).
The element
\(z_i=f_i^{1/2}w_ip_i\), extended by zero outside the neighborhood,
is continuous and satisfies
\[
z_iz_i^*=f_ip,\qquad z_i^*z_i=f_ip_i.
\]
The quasitrace identity therefore gives
\(\rho(f_ip)=\rho(f_ip_i)\).

The functional \(\rho_i(b)=\rho(f_i b)\), with \(b\) viewed as a
constant section, is a bounded 2-quasitrace on \(B\). Additivity on
commuting self-adjoint elements is preserved by the central weight.
The identity for \(b^*b\) and \(bb^*\) follows by applying the
quasitrace identity to \(f_i^{1/2}b\), and the same argument at
matrix level supplies its 2-quasitrace extension.
Its value at the unit is \(\rho(f_i)\).
If this value is positive, normalize \(\rho_i\) and apply the
hypothesis; if it is zero, positivity gives \(\rho_i(p_i)=0\).
Thus
\[
\rho(f_ip_i)\le c\,\rho(f_i).
\]
The elements \(f_ip\) commute with each other, as do the \(f_i\).
Quasitrace additivity on these commuting families yields
\[
\rho(p)=\sum_i\rho(f_ip)
       \le c\sum_i\rho(f_i)=c.
\]
This proves (13). \(\square\)

Now assume the hypotheses of Theorem 2 and set \(N=d+1\).
[Seth--Vilalta, Theorem A](https://arxiv.org/html/2602.14809v1)
proves that \(A=C(X,B)\) is pure when \(X\) is compact metric and
\(B\) is simple pure. Finite CW complexes satisfy the base hypothesis.
Consequently \(A\) has strict comparison.

By Lemma 4, for every normalized bounded 2-quasitrace \(\rho\) on \(A\),
\[
(N-1)\rho(p)\le(N-1)c<1-c\le\rho(1-p).
\tag{14}
\]
Both \(p\) and \(1-p\) are full in \(A\), by the nonzero proper
fiber hypothesis and the fullness argument in Section 3.
Strict comparison now gives
\[
(N-1)[p]\le[1-p],
\]
which is exactly (2).

To check the normalization convention in strict comparison, take
any lower semicontinuous 2-quasitrace with
\(d_\rho(1-p)=1\). Fullness of the projection \(1-p\) gives
\([1]\le M[1-p]\) for some integer \(M\), so \(\rho(1)\) is finite
and nonzero. Normalize it on \(1\) and apply (14). Thus (14)
verifies also the normalized dimension-function form of strict
comparison; it is not restricted to an insufficient class of
functionals. Theorem 1 completes the proof of Theorem 2.

## 5. Scope of the advance and the remaining obstruction

The existing endpoint-matrix result contracts families already
supported in a fixed sufficiently large hereditary matrix piece.
Here the support itself may be a nontrivial projection bundle
over the parameter space. The proof creates an actual finite
matrix corner around that varying support and uses its explicit
stable-rank bound. Under (3), strict comparison supplies the needed
orthogonal copies.

This does not move an arbitrary stably null family into such a
support. In particular, a positive hereditary cutoff is not an
actual projection and cannot be substituted for \(p\) in (8)--(10).
The earlier norm obstruction to replacing soft support by
projections remains relevant. For a projectionless \(B\), there
are no nonzero proper \(B\)-valued projection supports of this
kind, so Theorem 2 makes no assertion about its general kernel.

The gap to full K-stability is therefore explicit: construct a
homotopy reducing the displacement of an arbitrary kernel family
to an eligible support, or find a replacement for the actual
projection matrix units used here. The present artifact proves
the contraction after a checkable projection comparison and,
in the pure case, after the quantitative bound (3); it does not
assume or assert global sphere fragmentation.

## 6. Sources

- M. A. Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*,
  Journal of Operator Theory 17 (1987), 237--254, Theorem 2.10,
  printed p. 243:
  [original paper](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf).
- M. A. Rieffel, *Dimension and stable rank in the K-theory of
  C*-algebras*, Proceedings of the London Mathematical Society
  46 (1983), 301--333:
  [DOI](https://doi.org/10.1112/plms/s3-46.2.301).
  The ideal, extension, and crossed-product bounds used here
  are also recorded with theorem references in
  [Blackadar, V.3.1.21--23](https://www.bruceblackadar.com/Mathematics/Cycr.pdf).
- A. Seth and E. Vilalta, *Continuous functions over a pure
  C*-algebra*, arXiv:2602.14809, Theorem A and Remark 3.3:
  [primary manuscript](https://arxiv.org/html/2602.14809v1).
  Its function-algebra purity theorem is prior art, already
  recorded elsewhere in this project; it is an input here.
- The fixed-piece contraction and the soft-support obstruction
  are in [the soft-module note](../../notes/stw58-soft-module-compression-attempt-2026-09-05.md).
