# Two finite-factor expectations and robust intersection

2026-09-08. Pure matrix arguments; no computation or build.

The fixed orders three and eight give an actual robust-intersection
theorem when the two averaging expectations approximately commute.
The original expectations in canonical Leavitt models fail that
hypothesis by a fixed amount. Long-heat near-idempotence does not
imply it either. None of these statements decides heat rounding or
hyperlinearity of the Leavitt unit group.

All traces and Hilbert--Schmidt norms are normalized in the ambient
matrix dimension. Write \(\|T\|_{\infty\to2}\) for the supremum over
operator-norm contractions.

## 1. A proved robust-intersection theorem for orders three and eight

Let \(E,F:M_d\to M_d\) be averaging expectations for unitary
representations of groups of orders three and eight, respectively.
Their ranges are the respective commutant algebras. Set

\[
\eta=\|EF-FE\|_{\infty\to2},\qquad \Psi=EFE.
\]

Then \(\Psi\) is self-adjoint bistochastic UCP, with Kraus rank at
most \(3\cdot8\cdot3=72\), and

\[
\Psi^2-\Psi=EF(EF-FE)E,\qquad
\|\Psi^2-\Psi\|_{\infty\to2}\leq\eta.       \tag{1}
\]

The norm estimate uses \(L^2\)-contractivity on the left and
operator-norm contractivity on the right. The
[proved bounded-Kraus-rank theorem, Section 12](leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md)
therefore supplies a dimension-independent modulus \(f_{72}(s)\to0\)
as \(s\downarrow0\), and a unital subalgebra \(D\subseteq M_d\)
with

\[
\|E_D-EFE\|_{\infty\to2}\leq f_{72}(\eta).   \tag{2}
\]

The modulus can be enlarged if necessary; no explicit rate is
claimed. At \(\eta=0\), take the exact intersection expectation.

This has the usual robust-intersection consequences. Put
\(\rho=f_{72}(\eta)\). Since

\[
EFE-EF=-E(EF-FE),\qquad
(I-F)EFE=(EF-FE)FE,
\]

we have

\[
\|E_D-EF\|_{\infty\to2}\leq\rho+\eta,
\]

and each contraction of \(D\) lies within \(\rho\) of the
operator unit ball of \(\operatorname{ran}E\), and within
\(\rho+\eta\) of that of \(\operatorname{ran}F\).
For any contraction \(x\) satisfying

\[
\|x-Ex\|_2\leq a,\qquad \|x-Fx\|_2\leq a,
\]

contractivity gives \(\|x-EFEx\|_2\leq3a\). Hence

\[
\operatorname{dist}_2(x,D_{\leq1})\leq3a+\rho.\tag{3}
\]

This is an established sufficient condition in normalized
Hilbert--Schmidt norm, not an additional open rounding premise.
The same argument works for finite orders \(r,s\), using Kraus
rank at most \(r^2s\).

## 2. The native canonical expectations stay away from commuting

Use the generating finite subgroups from the
[24k chart](leavitt-24k-relative-unitary-reduction-2026-09-08.md):

\[
A=\langle c\rangle\cong C_3,\qquad
B=\{x_{12}(r):r\in V\}\cong C_2^3,
\quad V=\operatorname{span}_{\mathbb F_2}\{s_0,t_0,v\},
\]

where \(c\) is the three-cycle permutation matrix. Then

\[
AB\cap BA=A\cup B,\qquad |AB\cap BA|=10.       \tag{4}
\]

Indeed, suppose
\(c^i x_{12}(r)=x_{12}(s)c^j\), with \(i,j\in\{0,1,2\}\).
The left side differs from the permutation matrix \(c^i\) in at
most one row, and the right side differs from \(c^j\) only in
row one. If \(i\ne j\), choose a row unaffected by both root
corrections. The two distinct powers of a three-cycle have their
ones in different columns on that row, a contradiction. Thus
\(i=j\). For \(i=0\) this gives precisely \(B\). For \(i\ne0\),
conjugation by \(c^i\) moves the root position \((1,2)\) to a
different position, so equality forces \(r=s=0\). The two
remaining elements are \(c,c^2\), proving (4).

Since \(A\cap B=\{1\}\), both product sets have size 24, and

\[
|AB\mathbin\triangle BA|=28.
\]

Now take any canonical matrix microstate sequence with these two
finite factors exact, as in the frozen chart. Let \(E_n,F_n\) be
their averaging expectations. The Haar Kraus-frame identity gives

\[
\begin{aligned}
\|E_nF_n-F_nE_n\|_{\infty\to2}^2
&\geq\int_{\mathcal U(d_n)}
       \|(E_nF_n-F_nE_n)(u)\|_2^2\,du\\
&=\left\|
 \frac1{24}\sum_{g\in AB}|V_{g,n}\rangle\langle V_{g,n}|
 -\frac1{24}\sum_{h\in BA}|V_{h,n}\rangle\langle V_{h,n}|
 \right\|_{\mathrm{HS}}^2.
\end{aligned}                                                     \tag{5}
\]

Here \(V_{g,n}\) denotes the indicated two-factor word evaluation;
the two frame sums may be interchanged depending on the convention
for conjugation, which leaves the norm unchanged. The frame norm is
the ordinary Hilbert-space Hilbert--Schmidt norm on
\(L^2(M_{d_n},\tau_{d_n})\).

Canonical word traces make their limiting Gram matrix identify equal
group elements and make distinct group elements orthogonal.
Thus the last line of (5) tends to

\[
\frac{24+24-2\cdot10}{24^2}=\frac7{144}.
\]

Consequently

\[
\boxed{\displaystyle
\liminf_n\|E_nF_n-F_nE_n\|_{\infty\to2}
 \geq\frac{\sqrt7}{12}.}                         \tag{6}
\]

The same argument applies along a tracial ultrafilter. It only uses
the canonical traces of a fixed finite list of words. In particular,
Section 1 cannot be applied directly to the original two native
expectations. This conclusion does not obstruct a different exact
algebra approximating their long heat.

## 3. An exact frozen-chart counterexample to two heat shortcuts

This example satisfies the precise regular-factor chart, but is not
asserted to satisfy the kernel relations of \(H\).

Work in dimension 24, in the joint character basis
\(\{|a,b\rangle:a\in\mathbb Z/3,\ b\in\mathbb F_2^3\}\).
Let

\[
C|a,b\rangle=\zeta^a|a,b\rangle,\qquad
D_j|a,b\rangle=(-1)^{b_j}|a,b\rangle,
\quad \zeta=e^{2\pi i/3}.
\]

The restrictions are regular multiples. Let \(E\) average the
\(C_3\) action and \(F^{\mathrm{diag}}\) the \(C_2^3\) action.
Choose the two orthogonal coordinate planes

\[
W_1=\operatorname{span}\{|0,0\rangle,|1,e_1\rangle\},\qquad
W_2=\operatorname{span}\{|0,e_2\rangle,|1,e_3\rangle\}.
\]

On each plane, the two diagonal averaging expectations restrict to
the usual diagonal expectation on \(M_2\). Define \(U_n\) to be
the real rotation of angle \(\pi/8\) on \(W_1\), the rotation
of angle \(\theta_n=n^{-2}\) on \(W_2\), and the identity on
the orthogonal complement, for \(n\geq2\). Let \(U_0\) keep
the first rotation and omit the second. Set

\[
F_n=\operatorname{Ad}(U_n)F^{\mathrm{diag}}
                         \operatorname{Ad}(U_n^*),\qquad
L_n=I-\tfrac12(E+F_n),\qquad P_n=e^{-nL_n}.
\]

All finite-factor representations remain exact regular multiples.
Write \(D_n=\operatorname{ran}E\cap\operatorname{ran}F_n\).

The elementary conjugation bound yields

\[
\|F_n-F_0\|_{\infty\to\infty}\leq4\theta_n,
\qquad \|L_n-L_0\|_{\infty\to\infty}\leq2\theta_n.
\]

Both heat semigroups are UCP contractions. Duhamel's formula gives
\(\|e^{-nL_n}-e^{-nL_0}\|_{\infty\to\infty}\leq2/n\).
The fixed finite-dimensional \(L_0\) has kernel \(D_0\) and a
strictly positive smallest nonzero eigenvalue \(\kappa_0\). Hence

\[
\|P_n-E_{D_0}\|_{\infty\to2}
 \leq\eta_n:=2/n+e^{-\kappa_0n}\longrightarrow0.  \tag{7}
\]

In particular \(\|P_n^2-P_n\|_{\infty\to2}\leq3\eta_n\).
These heats do round to an exact algebra expectation.

Nevertheless the original two expectations do not approximately
commute. Let \(Z_1\) be Pauli \(Z\) on \(W_1\), zero outside.
It is a contraction. In the Bloch-plane calculation at angle
\(\pi/8\),

\[
EF_n(Z_1)-F_nE(Z_1)=-\tfrac12X_1.
\]

Since \(\|X_1\|_{2,24}=1/\sqrt{12}\),

\[
\|EF_n-F_nE\|_{\infty\to2}\geq\frac1{2\sqrt{12}}.
                                                               \tag{8}
\]

Nor is the exact coordinate intersection the correct heat limit.
The projection onto \(W_2\) belongs to \(D_n\). On that corner,
the two distinct diagonal algebras have scalar intersection for
every \(\theta_n\ne0\). Thus, for Pauli \(Z_2\) on \(W_2\),

\[
E_{D_n}(Z_2)=0,\qquad E_{D_0}(Z_2)=Z_2.
\]

The first equality also follows from bimodularity of \(E_{D_n}\)
over the projection onto \(W_2\). Equation (7) now gives

\[
\|P_n-E_{D_n}\|_{\infty\to2}
 \geq\frac1{\sqrt{12}}-\eta_n.                  \tag{9}
\]

Thus neither approximate commutation of the original expectations
nor approximation by their exact intersection follows from
long-heat near-idempotence, even in the regular \(24\)-dimensional
chart. Tensoring the entire example with the identity on
\(\mathbb C^k\) puts it in dimension \(24k\) with the same
bounds.

## 4. Literature scope

[Ranard--Walter--Witteveen, Theorem 6.9](https://arxiv.org/html/2603.08702v1)
constructs a robust algebra intersection from approximately commuting
conditional expectations in the operator norm for maps, or the
completely bounded norm. Section 1 supplies a tracial-norm version
for the present bounded finite-group orders using the already proved
bounded-Kraus theorem. Section 2 shows that even its weaker
commutator hypothesis fails on the original native pair. An argument
using modified expectations or a different extracted algebra would
still require additional work.
