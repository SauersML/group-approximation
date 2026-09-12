# STW LVIII: soft hereditary supports with an orthogonal reservoir

Date: 2026-09-05. **Complete proof; internal mathematical review completed.**
No external peer review, formal verification, or novelty priority is claimed.
This extends supported-kernel contraction to positive hereditary supports.
It does not localize every family and does not solve STW LVIII.

## 1. Statement

Let \(X\) be a compact metric space of finite covering dimension
\(d\ge1\), let \(B\) be a unital C*-algebra of stable rank one,
and put \(A=C(X,B)\). For \(h\in A_+\), write
\(\operatorname{Her}(h)=\overline{hAh}\).

**Theorem 1 (soft-support contraction).** Let \(h,b\in A_+\) satisfy
\[
h\text{ is full in }A,\qquad hb=0,\qquad
(N-1)[h]\le[b]\text{ in }\mathrm{Cu}(A)
\tag{1}
\]
for an integer \(N\ge d+1\). If \(u\in U(A)\) satisfies
\[
u-1\in\operatorname{Her}(h),\qquad [u]=0\text{ in }K_1(A),
\tag{2}
\]
then \(u\in U_0(A)\).

Neither \(h\) nor \(b\) is required to have a spectral gap.
No support projection is assumed to belong to \(A\), and no
nonzero projection inside \(B\) is used.

If \(B\) is unital simple finite pure, it has stable rank one by
Lin's theorem, so it is included. In that case \(A\) is pure by
Seth--Vilalta. Consequently (1)'s comparison can instead be checked
by strict comparison:
\[
(N-1)d_\rho(h)<d_\rho(b)
\tag{3}
\]
for the lower semicontinuous 2-quasitraces normalized by
\(d_\rho(b)=1\), provided \(b\) is full. Section 5 also gives a
sufficient condition using only fiber quasitraces.

For \(X=S^k\), stable nullness of a based family means zero of its
reduced \(K_1(C(S^k,B))\)-class: split evaluation identifies that
kernel with \(K_{k+1}(B)\). Thus (2) applies to a based sphere
family with zero stable homotopy class. The final contraction can
be made based.

## 2. Stable rank of every hereditary subalgebra of the function algebra

**Lemma 2.** Every hereditary subalgebra \(D\subset C(X,B)\) satisfies
\[
\operatorname{sr}(D)\le d+1.
\tag{4}
\]

**Proof.** Such a \(D\) is invariant under multiplication by \(C(X)\).
Its evaluation image \(D_x\) is a hereditary subalgebra of \(B\),
and has stable rank one. Enlarge \(D\) to
\[
E=D+C(X)1_B\subset C(X,B).
\tag{5}
\]
This is a closed unital C*-subalgebra, with \(D\) an ideal.
For example, the sum is closed because its image modulo \(D\)
is a quotient of the C*-algebra \(C(X)\).

The algebra \(E\) is a continuous field: all its elements are
norm-continuous \(B\)-valued functions. Its fiber is
\[
E_x=D_x+\mathbb C1_B.
\]
To check the fiber identification, an element of \(E\) vanishing
at \(x\) is uniformly approximated by its products with scalar
functions vanishing near \(x\). Hence the evaluation kernel is
exactly the defining \(C(X)\)-fiber ideal.

If \(D_x\) is nonunital, \(E_x\) is its minimal unitization.
If \(D_x\) is unital with proper unit \(p_x\), then
\(E_x\cong D_x\oplus\mathbb C\). If \(D_x=B\), then \(E_x=B\);
if \(D_x=0\), then \(E_x=\mathbb C\).
In every case \(\operatorname{sr}(E_x)=1\).

Ng--Sudo's continuous-field stable-rank theorem gives
\[
\operatorname{sr}(E)
 \le\sup_{x\in X}
   \operatorname{sr}\bigl(C([0,1]^d)\otimes E_x\bigr).
\tag{6}
\]
Its hypotheses hold here: \(X\) is compact metric and finite
dimensional, the fibers are unital, and \(E\) is the full algebra
of sections for its continuity structure. The latter maximality
can also be checked directly: a section locally uniformly
approximable by sections of \(E\) is globally approximable using
a finite central partition of unity, and hence belongs to \(E\).

Embed the cube as a closed subset of a coordinate chart in
\(\mathbb T^d\). The quotient estimate and \(d\) successive
trivial crossed products by \(\mathbb Z\) imply
\[
\operatorname{sr}\bigl(C([0,1]^d)\otimes E_x\bigr)\le d+1.
\]
Finally, the stable rank of an ideal is at most that of the
ambient algebra, so \(\operatorname{sr}(D)\le\operatorname{sr}(E)\).
This proves (4). \(\square\)

The input (6) is published prior art:
[Ng--Sudo, Theorem 1.2](https://arxiv.org/pdf/math/0205119),
*On the stable rank of algebras of operator fields over metric spaces*,
Journal of Functional Analysis 220 (2005), 228--236,
[DOI](https://doi.org/10.1016/j.jfa.2004.10.020).
The theorem is also applied to continuous fields in
[Antoine--Bosa--Perera--Petzka, Theorem 1.11](https://arxiv.org/pdf/1305.7495).
No general monotonicity of higher stable rank under arbitrary
hereditary inclusions is presumed in this argument.

## 3. Cuntz comparison constructs actual soft matrix copies

**Lemma 3.** Under (1), for every \(\varepsilon>0\) with
\(a=(h-\varepsilon)_+\ne0\), there is a hereditary subalgebra
\(R\subset A\) and an isomorphism
\[
\Phi:M_N(D_\varepsilon)\longrightarrow R,\qquad
D_\varepsilon=\operatorname{Her}(a),
\tag{7}
\]
whose first diagonal corner is the original inclusion of
\(D_\varepsilon\) in \(A\).

**Proof.** Apply the cutdown form of Rørdam's lemma to
\((N-1)[h]\le[b]\). In rectangular-matrix form it gives elements
\(x_2,\ldots,x_N\in A\) with
\[
x_i^*x_j=
 \begin{cases}a&i=j,\\0&i\ne j,\end{cases}
\qquad
\sum_{i=2}^Nx_ix_i^*\in\operatorname{Her}(b).
\tag{8}
\]
Here is why the rectangular form is legitimate. Apply the lemma
in a common matrix algebra to \(\operatorname{diag}(h,\ldots,h)\)
and to \(b\) in a single coordinate. The resulting element has
its range in that coordinate, because its range positive element
belongs to the hereditary algebra of the single-coordinate \(b\).
Its nonzero row gives (8).

The exact cutdown lemma, with no stable-rank assumption, is
[Rørdam's lemma, Theorem 2.7(iv), printed pp. 141--142](https://ems.press/content/serial-article-files/52386):
Cuntz comparison gives \(x^*x=(a-\varepsilon)_+\) and
\(xx^*\) in the target hereditary algebra. Its original source
is Rørdam's 1992 Proposition 2.4.

Set \(x_1=a^{1/2}\), and write the polar decompositions
\(x_i=v_i a^{1/2}\) in \(A^{**}\), with \(v_1\) the support of \(a\).
All \(v_i\) have the same initial projection. Their range
projections are pairwise orthogonal: for \(i,j\ge2\) this follows
from \(x_i^*x_j=0\), and orthogonality to the first range follows
from \(hb=0\). Therefore
\[
\Phi((z_{ij}))=\sum_{i,j=1}^N v_i z_{ij}v_j^*
\tag{9}
\]
is an injective *-homomorphism on \(M_N(D_\varepsilon)\).

Although the \(v_i\) need not lie in \(A\), every term in (9) does.
Indeed, approximate \(z\in D_\varepsilon\) by elements
\(a^{1/2}ya^{1/2}\); their images are \(x_i y x_j^*\in A\).
This also proves norm continuity of (9) on its domain.

Put \(c=\sum_{i=1}^Nx_ix_i^*\).
The image of (9) is exactly \(\operatorname{Her}(c)\).
To check the nontrivial inclusion, choose a positive contractive
approximate identity \(e_\ell=f_\ell(a)\) for
\(D_\varepsilon\), with each \(f_\ell\) vanishing near zero.
The elements
\[
F_\ell=\sum_i v_i e_\ell v_i^*
\]
form an approximate identity of \(\operatorname{Her}(c)\).
For \(z\in A\), all matrix coefficients of \(F_\ell zF_\ell\)
under (9) belong to \(D_\varepsilon\): the expressions
\(v_i e_\ell=x_i g_\ell(a)\) belong to \(A\), and compression
by the initial support places their products in
\(\operatorname{Her}(a)\).
Thus \(F_\ell A F_\ell\) lies in the image, and taking limits
proves the assertion. Since \(v_1\) is the support of \(a\),
the first diagonal corner is unchanged. \(\square\)

This construction uses exact equality of positive initial
elements in (8), not cancellation of Cuntz classes into
unavailable projections.

## 4. Proof of soft-support contraction

Fullness of \(h\) in the unital algebra \(A\) implies fullness
of \((h-\varepsilon)_+\) for every sufficiently small
\(\varepsilon>0\). Indeed, choose a finite sum
\(\sum_j a_jhb_j\) close enough to \(1_A\) to be invertible.
The same sum with \(h\) replaced by \((h-\varepsilon)_+\)
remains invertible for small \(\varepsilon\), so the ideal
generated by that cutdown contains an invertible element.

The hereditary algebras \(D_\varepsilon\) increase densely to
\(\operatorname{Her}(h)\) as \(\varepsilon\) decreases to zero.
Thus (2) allows an arbitrarily small \(\varepsilon\), with
\(D_\varepsilon\) full, and \(z\in D_\varepsilon\) such that
\[
\|1+z-u\|<1/10.
\]
The invertible \(1+z\) has polar unitary \(w\in1+D_\varepsilon\).
Its distance from \(u\) is less than \(1/5\): the polar correction
has norm at most \(1/10\), since the singular values of \(1+z\)
lie in \((9/10,11/10)\).
The polar part of the straight-line invertible path from \(u\)
to \(1+z\) is a homotopy from \(u\) to \(w\). Hence \(w\) also
has zero \(K_1(A)\)-class.

Use Lemma 3 for this cutdown. The algebra \(R\) contains the full
hereditary algebra \(D_\varepsilon\), and is itself full hereditary
in \(A\). Consequently
\[
K_1(R)\longrightarrow K_1(A)
\]
is an isomorphism. Under (7), \(w\) is the supported inclusion
of \(\operatorname{diag}(w,1,\ldots,1)\) at matrix size \(N\).
It therefore has zero class in \(K_1(M_N(D_\varepsilon))\).

By Lemma 2,
\(\operatorname{sr}(D_\varepsilon)\le d+1\le N\).
Rieffel's degree-zero stable-range theorem now contracts this
unitary at size \(N\). For nonunital \(D_\varepsilon\), apply
the theorem to its unitization and then remove the scalar
quotient along the path:
\[
H(t)\longmapsto H(t)\,j(q(H(t)))^*.
\tag{10}
\]
Here \(q\) is the scalar matrix quotient and \(j\) its scalar
section. Equation (10) stays in \(1+M_N(D_\varepsilon)\) and
preserves both endpoints, whose scalar parts are already \(1_N\).
This yields the contraction in \(1+R\subset A\), and the preceding
homotopy from \(u\) to \(w\) proves Theorem 1.

If a sphere family is based at \(x_0\), normalize the resulting
homotopy by \(H(x,t)H(x_0,t)^*\). The endpoints stay fixed and
the homotopy becomes based. No fixed-basepoint support condition
on \(h\) is needed.

## 5. A fiberwise quantitative condition in the pure case

Suppose \(B\) is unital simple finite pure, and \(h,b\) are full
orthogonal positive contractions in \(C(X,B)\).
Assume \(\mathrm{QT}_1(B)\ne\varnothing\), and suppose there are
numbers \(\alpha,\beta\) with
\[
(N-1)\alpha<\beta,\qquad
d_\tau(h(x))\le\alpha,\qquad d_\tau(b(x))\ge\beta
\tag{11}
\]
for every \(x\in X\) and every \(\tau\in\mathrm{QT}_1(B)\).
Then Theorem 1 applies.

Here is the required passage from fiber quasitraces to global
ones. For every positive section \(a\) and every normalized
quasitrace \(\rho\) on \(C(X,B)\),
\[
\inf_{x,\tau}\tau(a(x))
 \le\rho(a)\le
\sup_{x,\tau}\tau(a(x)).
\tag{12}
\]
Choose a finite cover on which \(a\) is within \(\eta\) of
a constant value \(a_i\), and a subordinate central partition
of unity \(f_i\). The functional
\(\rho_i(z)=\rho(f_i z)\) on constant coefficients is a
2-quasitrace with value \(\rho(f_i)\) at the unit. Monotonicity
and additivity on commuting positive elements give
\[
|\rho(f_i a)-\rho(f_i a_i)|\le\eta\rho(f_i).
\]
The \(f_i a\) commute with one another, so summation and
\(\sum_i\rho(f_i)=1\), followed by \(\eta\to0\), prove (12).

Apply (12) to \(h^{1/n}\). Since its fiber quasitrace values are
bounded by \(\alpha\), it follows that \(d_\rho(h)\le\alpha\).
For \(b\), fix \(\beta'<\beta\). The continuous functions
\[
(x,\tau)\longmapsto\tau(b(x)^{1/n})
\]
increase pointwise to values at least \(\beta\) on the compact
space \(X\times\mathrm{QT}_1(B)\). A finite-subcover argument
therefore gives one \(n\) for which all these values exceed
\(\beta'\). Equation (12) implies \(\rho(b^{1/n})\ge\beta'\).
Letting \(\beta'\uparrow\beta\) yields \(d_\rho(b)\ge\beta\).

The primary source for order preservation and the uniform continuity
used above is Blackadar--Handelman, Corollary II.2.5(ii)--(iii),
printed p. 324. In particular, normalized quasitraces are
1-Lipschitz on self-adjoint elements. Compactness of the normalized
quasitrace space is stated on printed p. 326 immediately before
Theorem II.4.4:
[original paper](https://ivv5hpp.uni-muenster.de/u/cuntz/Blackadar_and_Handelman-1.pdf).

One can also check this compactness directly. Regard a normalized
2-quasitrace together with a quasitrace extension to \(M_2(B)\)
as a pair of pointwise functions. The norm bounds place these
pairs in a product of compact disks; the defining quasitrace
identities, normalization, and restriction identity are closed
conditions. Tychonoff compactness, followed by projection to the
first function, proves compactness of \(\mathrm{QT}_1(B)\).
The Lipschitz estimate then makes
\((x,\tau)\mapsto\tau(b(x)^{1/n})\) jointly continuous, as required.

Seth--Vilalta's theorem makes \(C(X,B)\) pure, so it has strict
comparison. By (11), all normalized global quasitraces satisfy
\((N-1)d_\rho(h)<d_\rho(b)\).
Fullness of \(b\) allows normalization on the unit: a lower
semicontinuous quasitrace with \(d_\rho(b)=1\) has finite nonzero
value on \(1\), since \([1]\le M[b]\) for some \(M\).
Thus these inequalities verify the full strict-comparison
criterion, yielding (1).

## 6. What remains

The result applies to genuinely soft supports and their
orthogonal positive reservoirs. It covers families that vary
over the base and does not require small projections in \(B\).

The unresolved step is to deform an arbitrary stably null
family so that its displacement belongs to a full hereditary
support \(h\) with an orthogonal reservoir satisfying (1).
The equality \(h_0+h_1=1\) for dimension-drop endpoint supports
does not provide this: those supports generally overlap, and
neither need contain the displacement of a given family.
Cutting them to become orthogonal can discard coefficients
needed by that family. No such discard or global fragmentation
is made in the proof above.

This proves a new explicit supported-kernel contraction
criterion, not a full K-stability conclusion.

## 7. Sources and relation to earlier artifacts

- B. Blackadar and D. Handelman, *Dimension functions and traces
  on C*-algebras*, J. Funct. Anal. 45 (1982), 297--340,
  Corollary II.2.5(ii)--(iii), printed p. 324, and the compactness
  statement immediately preceding Theorem II.4.4, printed p. 326:
  [primary paper](https://ivv5hpp.uni-muenster.de/u/cuntz/Blackadar_and_Handelman-1.pdf),
  [DOI](https://doi.org/10.1016/0022-1236(82)90009-X).

- P. W. Ng and T. Sudo, *On the stable rank of algebras of operator
  fields over metric spaces*, J. Funct. Anal. 220 (2005), 228--236,
  Theorem 1.2:
  [primary preprint](https://arxiv.org/pdf/math/0205119),
  [published DOI](https://doi.org/10.1016/j.jfa.2004.10.020).
- M. Rørdam, *On the structure of simple C*-algebras tensored with
  a UHF-algebra. II*, J. Funct. Anal. 107 (1992), 255--269,
  Proposition 2.4. The exact formulation and proof used here are
  reproduced in Gardella--Perera, *The modern theory of Cuntz
  semigroups of C*-algebras*, EMS Surveys in Mathematical Sciences
  13 (2026), 133--214,
  [Theorem 2.7(iv), printed pp. 141--142](https://ems.press/content/serial-article-files/52386).
- M. A. Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*, J. Operator Theory 17 (1987), 237--254,
  [Theorem 2.10, printed p. 243](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf).
- A. Seth and E. Vilalta, *Continuous functions over a pure
  C*-algebra*, [Theorem A and Remark 3.3](https://arxiv.org/html/2602.14809v1).
- The earlier
  [varying-projection support theorem](stw58-small-projection-support-kernel-contraction-2026-09-05.md)
  used actual projection copies. The present theorem replaces
  them by cutdown hereditary copies and a continuous-field
  stable-rank bound. The
  [soft-module note](../../notes/stw58-soft-module-compression-attempt-2026-09-05.md)
  explains why replacing soft supports by norm-close projections
  is not an available alternative.
