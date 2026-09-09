# Reversing approximate inclusion for finite matrix algebras

2026-09-08. A dimension-independent finite-dimensional theorem, proved
below. The matrix-factor case was independently checked by two other
agents. The regular-trace, bounded-distortion, bounded-block, and
countable-flow extensions, including the atomic-center
characterization, also passed independent audits. No code was run
and no new formal verification is claimed.
The theorem supplies a conditional analytic bridge for the native
Leavitt compression argument; it does not determine hyperlinearity.

## 1. Statement and conventions

Equip \(M_d(\mathbb C)\) with normalized trace \(\tau\). Every
conditional expectation below preserves this trace. For a linear map
\(T:M_d\to M_d\), write

\[
\|T\|_{\infty\to2}
=\sup_{\|x\|_{\rm op}\leq1}\|T(x)\|_2.
\]

Let \(\mathcal A\subset M_d\) be a unital finite-dimensional
\(*\)-subalgebra,
let \(\mathcal B=U\mathcal A U^*\), and put
\(E=E_{\mathcal A}\), \(F=E_{\mathcal B}\). Write abstractly

\[
\mathcal A=\bigoplus_{j=1}^kM_{a_j}(\mathbb C),\qquad
\tau|_{\mathcal A}=\sum_j t_j\tau_{a_j},\qquad
D=\sum_j a_j^2,
\tag{1}
\]

where \(t_j>0\), \(\sum_jt_j=1\), and \(\tau_{a_j}\) is normalized.
Define the trace-weight distortion

\[
w_j=\frac{t_j}{a_j^2},\qquad
R=\frac{\max_jw_j}{\min_jw_j}\geq1.
\tag{2}
\]

**Theorem.** One has

\[
\boxed{\quad
\|EF-F\|_{\infty\to2}
\leq\min\left\{1,\sqrt{2R}\,
\|FE-E\|_{\infty\to2}\right\}.
\quad}
\tag{3}
\]

Call the trace in (1) **regular** when
\(t_j=a_j^2/D\) for every \(j\). Then \(R=1\), so the bound is
\(\min\{1,\sqrt2\,\delta\}\) when the forward error is at most
\(\delta\). In particular this holds for every matrix factor
\(\mathcal A\cong M_a\), independently of \(a\), its multiplicity
in \(M_d\), and \(d\).

No approximate multiplicativity, stability theorem, or spectral gap
is an assumption of (3). Its hypotheses concern exact algebras and
their exact conditional expectations.

## 2. Haar mean controls the largest unitary leakage

First allow \(\mathcal A,\mathcal B\subset M_d\) to be arbitrary
unital finite-dimensional \(*\)-subalgebras. Define

\[
d_{\mathcal A,\mathcal B}(u)
=\|(I-F)u\|_2^2,\qquad
\alpha_{\mathcal A,\mathcal B}
=\int_{\mathcal U(\mathcal A)}d_{\mathcal A,\mathcal B}(u)\,du.
\tag{4}
\]

All Haar measures are probability measures. Haar averaging conjugation
by \(\mathcal U(\mathcal B')\) is \(F\), where the commutant is
taken inside \(M_d\). Since \(F\) is the orthogonal projection onto
\(L^2(\mathcal B)\), for a unitary \(u\in\mathcal A\),

\[
d_{\mathcal A,\mathcal B}(u)
=\frac12\int_{\mathcal U(\mathcal B')}
\|[u,v]\|_2^2\,dv.
\tag{5}
\]

For any fixed \(v\in M_d\) and \(u\in\mathcal U(\mathcal A)\),
the element \(E_{\mathcal A'}v\) commutes with \(u\), so

\[
\|[u,v]\|_2^2
\leq4\|v-E_{\mathcal A'}v\|_2^2.
\tag{6}
\]

On the other hand, direct expansion and Haar averaging give

\[
\int_{\mathcal U(\mathcal A)}\|[u,v]\|_2^2\,du
=2\|v-E_{\mathcal A'}v\|_2^2.
\tag{7}
\]

Insert (6) into (5) and use (7). This proves the useful general lemma

\[
\boxed{\quad
\sup_{u\in\mathcal U(\mathcal A)}d_{\mathcal A,\mathcal B}(u)
\leq2\alpha_{\mathcal A,\mathcal B}.
\quad}
\tag{8}
\]

The unit ball of a finite-dimensional unital algebra is the convex
hull of its unitaries. Indeed, complete the polar partial isometry of
a contraction \(x\) to a unitary \(w\), and set
\(h=|x|+i(1-|x|^2)^{1/2}\); then
\(x=(wh+wh^*)/2\). Since \(E\) maps the ambient operator unit ball
onto the operator unit ball of \(\mathcal A\), it follows that

\[
\|FE-E\|_{\infty\to2}^2
=\sup_{u\in\mathcal U(\mathcal A)}
d_{\mathcal A,\mathcal B}(u).
\tag{9}
\]

The same statements hold with \(\mathcal A,\mathcal B\) interchanged.
Thus the remaining issue is to compare the two Haar means, rather
than the two largest leakages directly.

## 3. Haar covariance and regular trace

Use the Hilbert space \(L^2(M_d,\tau)\), and let
\(\operatorname{Tr}_{\rm HS}\) denote the ordinary, unnormalized
trace of a linear operator on this Hilbert space. This is a
superoperator trace, distinct from the normalized matrix trace
\(\tau\).

On block \(j\) of \(\mathcal A\), an orthonormal basis is

\[
f_{pq}^{(j)}=\sqrt{a_j/t_j}\,e_{pq}^{(j)}.
\]

For Haar \(u=(u_j)_j\in\mathcal U(\mathcal A)\), its coordinates
in this basis have covariance

\[
\int \langle f_{pq}^{(j)},u\rangle
\overline{\langle f_{rs}^{(l)},u\rangle}\,du
=\boldsymbol 1_{j=l}\boldsymbol 1_{p=r}\boldsymbol 1_{q=s}
\frac{t_j}{a_j^2}.
\tag{10}
\]

Here one uses the elementary Haar entry identity
\(\int (u_j)_{pq}\overline{(u_j)_{rs}}\,du_j
=\delta_{pr}\delta_{qs}/a_j\); different blocks have independent
scalar phases and hence zero cross covariance. Let
\(C_{\mathcal A}\) be this covariance operator, extended by zero
on \(L^2(\mathcal A)^\perp\). It follows that

\[
w_{\min}E\leq C_{\mathcal A}\leq w_{\max}E,
\qquad
\alpha_{\mathcal A,\mathcal B}
=\operatorname{Tr}_{\rm HS}\bigl(C_{\mathcal A}(I-F)\bigr).
\tag{11}
\]

The inequalities are inequalities of positive operators. Consequently,
with
\(s=\operatorname{Tr}_{\rm HS}(E(I-F))\),

\[
w_{\min}s\leq\alpha_{\mathcal A,\mathcal B}
\leq w_{\max}s.
\tag{12}
\]

If the trace is regular, (10) says simply
\(C_{\mathcal A}=E/D\), and hence

\[
\alpha_{\mathcal A,\mathcal B}
=1-\frac{\operatorname{Tr}_{\rm HS}(EF)}D.
\tag{13}
\]

This exact identity is where regular trace enters the argument.

## 4. Proof of reversal

Return to \(\mathcal B=U\mathcal A U^*\). The algebras have the
same dimension \(D\), the same trace weights, and the same bounds
\(w_{\min},w_{\max}\). Moreover

\[
\operatorname{Tr}_{\rm HS}(F(I-E))
=D-\operatorname{Tr}_{\rm HS}(FE)
=\operatorname{Tr}_{\rm HS}(E(I-F))=s.
\tag{14}
\]

Equations (12) and (14) imply
\(\alpha_{\mathcal B,\mathcal A}
\leq R\alpha_{\mathcal A,\mathcal B}\). Applying (8) and (9) in
the reverse direction now yields

\[
\begin{aligned}
\|EF-F\|_{\infty\to2}^2
&\leq2\alpha_{\mathcal B,\mathcal A}\\
&\leq2R\alpha_{\mathcal A,\mathcal B}\\
&\leq2R\|FE-E\|_{\infty\to2}^2.
\end{aligned}
\tag{15}
\]

The bound by one in (3) follows because \(I-E\) is an orthogonal
projection on \(L^2(M_d)\), and \(F\) sends contractions to
contractions. This proves the theorem.

In the regular case, (13) and cyclicity of the superoperator trace
give equality of the two Haar means. Equivalently, one may view the
factor case through the bistochastic channel
\(T=E\operatorname{Ad}U|_{\mathcal A}\): the forward and reverse
energies use \(TT^*\) and \(T^*T\), whose superoperator traces
coincide. The Haar covariance proof also handles multiple central
blocks with exactly the stated weights.

## 5. Finite-group algebras and their commutants

Suppose \(G\) is finite and \(\pi=m\lambda_G\), with irreducible
dimensions \(d_j\). Then

\[
\pi(\mathbb C[G])
\cong\bigoplus_j M_{d_j}\otimes I_{m d_j},\qquad
\tau(z_j)=\frac{d_j^2}{|G|}.
\tag{16}
\]

Since \(\sum_jd_j^2=|G|\), this algebra has regular trace. Its
commutant is

\[
\pi(\mathbb C[G])'
\cong\bigoplus_j I_{d_j}\otimes M_{m d_j}.
\tag{17}
\]

Its abstract dimension is \(m^2|G|\), and its central weights are
also regular:
\(d_j^2/|G|=(m d_j)^2/(m^2|G|)\).

More generally, write an embedded algebra as
\(\bigoplus_j M_{a_j}\otimes I_{b_j}\), where
\(d=\sum_ja_jb_j\). Regular trace is equivalent to
\(b_j=(d/D)a_j\) for every \(j\). Its commutant then has regular
trace as well, since all multiplicities are in the same proportion.
Thus the theorem applies to both sides of these exact mutual
commutant pairs.

For arbitrary multiplicities, the distortion (2) is unchanged by
taking the commutant: the covariance weights are respectively
\(b_j/(d a_j)\) and \(a_j/(d b_j)\), whose maximum-to-minimum ratios
are equal.

For an exact finite-group representation with the canonical trace
\(\tau(\pi(g))=\delta_{g,1}\), character orthogonality gives a
multiple of the regular representation and hence (16). These are
exact statements; approximate traces alone have not been used to
replace an arbitrary tuple by an exact representation.

## 6. A quantitative bridge for heat maps

Let \(P:M_d\to M_d\) be unital, completely positive and
trace-preserving, and let
\(Q=\operatorname{Ad}U\,P\,\operatorname{Ad}U^*\). Suppose

\[
\|QP-P\|_{\infty\to2}\leq\delta,\qquad
\|P-E_{\mathcal A}\|_{\infty\to2}\leq\eta.
\tag{18}
\]

Then \(\|Q-F\|_{\infty\to2}\leq\eta\), for
\(F=E_{U\mathcal A U^*}\). The maps \(P,Q,E,F\) all contract
operator norm and \(L^2\). Expand

\[
FE-E=(F-Q)P+F(E-P)+(QP-P)+(P-E).
\]

The first error term is bounded using the operator-norm contraction
of \(P\), and the second using the \(L^2\) contraction of \(F\).
It follows that
\(\|FE-E\|_{\infty\to2}\leq\delta+3\eta\).
Reversal and the same three-error comparison in the other direction
give

\[
\boxed{\quad
\|PQ-Q\|_{\infty\to2}
\leq3\eta+\sqrt{2R}\,(\delta+3\eta).
\quad}
\tag{19}
\]

In particular, vanishing forward error and a vanishing uniform
\(\infty\to2\) approximation by expectations onto algebras with
bounded \(R\) force vanishing reverse error. This applies to the
native conjugate heat maps if precisely that approximation is
established.

## 7. Discarding a small central part

The distortion need not be controlled on every central block. Let
\(p\in Z(\mathcal A)\) be nonzero, with \(\tau(p)=1-s\), and
let \(R_p\) be the distortion of \(p\mathcal A p\) with its
normalized corner trace. If \(\delta=\|FE-E\|_{\infty\to2}\), then

\[
\boxed{\quad
\|EF-F\|_{\infty\to2}
\leq\min\left\{1,
\sqrt{2R_p\delta^2+2(R_p+1)s}\right\}.
\quad}
\tag{20}
\]

To prove this, put \(q=UpU^*\) and decompose the Hilbert-space
projections into their central parts:

\[
E=P_0+P_1,\qquad F=Q_0+Q_1,
\]

where \(P_0\) projects onto \(p\mathcal A\), \(P_1\) onto
\((1-p)\mathcal A\), and \(Q_0,Q_1\) onto the corresponding
conjugate subspaces. Let \(C_{\mathcal A,0}\) be the ambient
\(L^2\) covariance of Haar unitaries of \(p\mathcal A\), extended
by zero outside \(L^2(p\mathcal A)\), and define
\(C_{\mathcal B,0}\) analogously. On their respective supporting
subspaces these covariances have the same smallest and largest
eigenvalues \(w_{\min},w_{\max}\), with
\(w_{\max}/w_{\min}=R_p\). Normalizing the corner trace scales
both eigenvalues by the same factor and does not change this ratio.

Write \(\alpha_{\mathcal A,0}\) for the Haar mean of
\(\|(I-F)u\|_2^2\) over unitaries \(u\) of \(p\mathcal A\)
(so \(u^*u=uu^*=p\)), and use the analogous notation for the
other three parts. Independence of the scalar Haar phases on the
two central parts gives

\[
\alpha_{\mathcal A,\mathcal B}
=\alpha_{\mathcal A,0}+\alpha_{\mathcal A,1},\qquad
\alpha_{\mathcal B,\mathcal A}
=\alpha_{\mathcal B,0}+\alpha_{\mathcal B,1}.
\tag{21}
\]

The small-part means are at most \(s\), since \(I-E\) and
\(I-F\) are orthogonal projections and each small-part unitary has
squared \(L^2\) norm \(s\). When \(s=0\), these terms are zero.
Equal ranks of \(P_0,Q_0\) imply

\[
s_0:=\operatorname{Tr}_{\rm HS}(P_0(I-Q_0))
=\operatorname{Tr}_{\rm HS}(Q_0(I-P_0)).
\]

Set \(c_{01}=\operatorname{Tr}_{\rm HS}(C_{\mathcal A,0}Q_1)\).
The covariance bounds give

\[
\begin{aligned}
\alpha_{\mathcal A,0}+c_{01}
&=\operatorname{Tr}_{\rm HS}(C_{\mathcal A,0}(I-Q_0))
 \geq w_{\min}s_0,\\
\alpha_{\mathcal B,0}
&\leq\operatorname{Tr}_{\rm HS}(C_{\mathcal B,0}(I-P_0))
 \leq w_{\max}s_0.
\end{aligned}
\tag{22}
\]

Moreover

\[
c_{01}=\int_{\mathcal U(p\mathcal A)}\|Q_1u\|_2^2\,du
\leq s.
\tag{23}
\]

Indeed, \(Q_1u=(1-q)F(u)\) is an operator contraction supported
on \(1-q\), whose trace is \(s\). Combining (21)--(23) gives

\[
\alpha_{\mathcal B,\mathcal A}
\leq R_p\alpha_{\mathcal A,0}+(R_p+1)s
\leq R_p\alpha_{\mathcal A,\mathcal B}+(R_p+1)s.
\tag{24}
\]

The general bound (8) on the largest unitary leakage now proves
(20). In particular, for a regular large corner, including a single
matrix-factor block, one has the sharper simple formula

\[
\|EF-F\|_{\infty\to2}^2\leq2\delta^2+4s.
\tag{25}
\]

Thus bounded distortion on a central part of trace tending to one
suffices for reversal when the forward error tends to zero. No
control is needed on the multiplicities or dimensions of the
discarded blocks.

## 8. A bounded number of central blocks also forces reversal

There is a second dimension-independent estimate that needs no
control of the trace-weight distortion. Suppose \(\mathcal A\)
has \(k\) minimal central projections. Then

\[
\boxed{\quad
\|EF-F\|_{\infty\to2}^2
\leq2k\,\|FE-E\|_{\infty\to2}^2.
\quad}
\tag{26}
\]

The improvement uses the physical overlaps of the central supports,
in addition to the superoperator overlaps from section 3.

Index the central blocks of \(\mathcal A\) by \(i=1,\ldots,k\),
with central supports \(p_i\), abstract degrees \(a_i\), physical
traces \(t_i=\tau(p_i)\), and weights \(w_i=t_i/a_i^2\).
Set \(q_i=Up_iU^*\). Let \(P_i,Q_i\) be the Hilbert-space
orthogonal projections onto \(p_i\mathcal A\) and
\(q_i\mathcal B\), respectively, and put

\[
m_{ij}=\tau(p_iq_j),\qquad
h_{ij}=\operatorname{Tr}_{\rm HS}(P_iQ_j).
\tag{27}
\]

Both matrices have nonnegative entries. The physical overlap matrix
has matching row and column marginals:
\(\sum_jm_{ij}=t_i\) and \(\sum_im_{ij}=t_j\).

For a Haar unitary \(u_i\) of \(p_i\mathcal A\), viewed as a
partial unitary in \(M_d\), the covariance calculation gives
\(\int\|Q_ju_i\|_2^2\,du_i=w_ih_{ij}\).
Furthermore \(Q_j=Q_j(q_j\,\cdot\,q_j)\) is an orthogonal
projection, so

\[
\|Q_ju_i\|_2^2
\leq\|q_ju_iq_j\|_2^2
\leq\tau(q_ju_i^*u_iq_j)
=\tau(p_iq_j)=m_{ij}.
\]

Repeating the calculation with a Haar unitary of
\(q_j\mathcal B\), projected onto \(p_i\mathcal A\), proves
the two crucial support bounds

\[
\boxed{\qquad w_ih_{ij}\leq m_{ij},\qquad
w_jh_{ij}\leq m_{ij}.\qquad}
\tag{28}
\]

The forward and reverse Haar means from (4) therefore have the
nonnegative decompositions

\[
\alpha_{\mathcal A,\mathcal B}
=\sum_{i,j}(m_{ij}-w_ih_{ij}),\qquad
\alpha_{\mathcal B,\mathcal A}
=\sum_{i,j}(m_{ij}-w_jh_{ij}).
\tag{29}
\]

Regard \(m\) as a balanced directed flow on these \(k\) vertices.
Define its upward and downward costs with respect to the weights
\(w_i\) by

\[
\begin{aligned}
\mathsf U&=\sum_{w_i<w_j}m_{ij}(1-w_i/w_j),\\
\mathsf D&=\sum_{w_i>w_j}m_{ij}(1-w_j/w_i).
\end{aligned}
\tag{30}
\]

For an upward edge, the second bound in (28) gives
\(m_{ij}-w_ih_{ij}\geq m_{ij}(1-w_i/w_j)\).
For a downward edge, the first bound gives
\((w_i-w_j)h_{ij}\leq m_{ij}(1-w_j/w_i)\).
Consequently

\[
\mathsf U\leq\alpha_{\mathcal A,\mathcal B},\qquad
\alpha_{\mathcal B,\mathcal A}
-\alpha_{\mathcal A,\mathcal B}\leq\mathsf D.
\tag{31}
\]

Every nonnegative balanced finite flow decomposes into directed
simple cycles with nonnegative coefficients. Each such cycle has
at most \(k\) vertices. Along one cycle, write its weights as
\(w_i=e^{\ell_i}\). The sum of the positive increments of
\(\ell\) equals the sum of the absolute negative increments.
The increasing function \(f(x)=1-e^{-x}\), \(x\geq0\), is
subadditive:

\[
f(x+y)=f(x)+e^{-x}f(y)\leq f(x)+f(y).
\]

Thus the cost of each individual downward edge is at most the sum
of the upward costs on that cycle. A nonconstant cycle has at most
\(k-1\) downward edges; a constant cycle contributes zero. Summing
over the cycle decomposition proves

\[
\mathsf D\leq(k-1)\mathsf U.
\tag{32}
\]

Equations (31)--(32) give
\(\alpha_{\mathcal B,\mathcal A}
\leq k\alpha_{\mathcal A,\mathcal B}\). Apply (8)--(9) to
deduce (26). In particular a uniformly bounded number of central
blocks rules out vanishing forward error with a positive limiting
reverse error, regardless of the simple block sizes or multiplicities.

## 9. Tight physical central weights force asymptotic reversal

The number of central blocks may grow, provided their physical trace
weights remain tight. More precisely, let
\(\mathcal B_n=U_n\mathcal A_nU_n^*\subset M_{d_n}\), let
\(E_n,F_n\) be their expectations, and list the central weights of
\(\mathcal A_n\) in nonincreasing order
\(t_{n,1}\geq t_{n,2}\geq\cdots\), padded by zeros. Assume

\[
\forall\epsilon>0\ \exists K<\infty:\quad
\limsup_{n\to\infty}\sum_{i>K}t_{n,i}<\epsilon.
\tag{33}
\]

Then

\[
\boxed{\quad
\|F_nE_n-E_n\|_{\infty\to2}\longrightarrow0
\quad\Longrightarrow\quad
\|E_nF_n-F_n\|_{\infty\to2}\longrightarrow0.
\quad}
\tag{34}
\]

The same assertion holds with limits and tightness taken along any
fixed free ultrafilter. No bound on the ratios of trace weights to
squared simple degrees is assumed.

Use the notation of (27)--(31) at each stage. If (34) failed, pass
to a subsequence on which the reverse error is bounded below. By a
diagonal extraction, assume all \(t_{n,i}\) and \(m_{n,ij}\)
converge, to \(t_i\) and \(m_{ij}\), respectively. Tightness gives

\[
\sum_i t_i=1,\qquad
\sum_jm_{ij}=t_i,\qquad\sum_im_{ij}=t_j.
\tag{35}
\]

For example, the missing row mass outside a finite set of columns
is bounded by \(\sum_{j>K}t_{n,j}\), which is uniformly small
after taking \(K\) large. This justifies passage of the marginals
to the limit. Vertices with \(t_i=0\) carry no limiting flow and
may be omitted.

For all remaining pairs, extract further so that
\(r_{ij}=\lim_n w_{n,i}/w_{n,j}\) exists in the compact extended
interval \([0,\infty]\). Each such block is present eventually,
because its limiting physical weight is positive. Since the forward
Haar mean tends to zero, (28)--(29) imply

\[
m_{ij}>0\quad\Longrightarrow\quad r_{ij}\geq1.
\tag{36}
\]

Indeed, if \(r_{ij}<1\), the upward edge contributes at least
\(m_{n,ij}(1-w_{n,i}/w_{n,j})\) to that mean for all sufficiently
large \(n\), giving a positive limiting contribution.

Every positive edge of the countable balanced flow (35) belongs
to a finite directed cycle of positive edges. To verify this for
\(i\to j\), let \(S\) be the vertices reachable from \(j\) by
finite positive-edge paths. This set has no outgoing flow. Equality
of incoming and outgoing flow across \(S\), which follows from
(35) and finite total mass, then gives no incoming flow either.
If \(i\notin S\), the edge \(i\to j\) contradicts that fact.
Thus a finite return path exists.

Around a finite cycle the finite-stage ratios multiply to exactly
one. Every limiting ratio on its edges is at least one by (36).
They must therefore all equal one; in particular none is infinite.
Consequently

\[
m_{ij}>0\quad\Longrightarrow\quad
\frac{w_{n,i}}{w_{n,j}}\longrightarrow1.
\tag{37}
\]

Define
\(c_{n,ij}=1-\min(w_{n,i},w_{n,j})/
\max(w_{n,i},w_{n,j})\) on present blocks, taking zero when an
index is absent. For each fixed pair,
\(m_{n,ij}c_{n,ij}\to0\): use (37) when \(m_{ij}>0\), and
\(0\leq c_{n,ij}\leq1\) otherwise. Moreover

\[
\sum_{i>K\ \text{or}\ j>K}m_{n,ij}c_{n,ij}
\leq2\sum_{i>K}t_{n,i}.
\]

Tightness and finite truncation now imply
\(\sum_{i,j}m_{n,ij}c_{n,ij}\to0\).
In particular the downward cost in (30) tends to zero. Equation
(31) shows that the reverse Haar mean tends to zero, and (8)
then forces the reverse norm to tend to zero, a contradiction.
The ultrafilter version has the identical proof using ultralimits
instead of subsequence extraction.

### Equivalent formulation through the ultraproduct center

Let \(\mathcal A_\omega=\prod_\omega\mathcal A_n\) be the
tracial ultraproduct using the physical traces. Its center is

\[
Z(\mathcal A_\omega)=\prod_\omega Z(\mathcal A_n).
\tag{38}
\]

One inclusion is immediate. For the other, the Haar commutator
identity gives, for every \(x_n\in\mathcal A_n\),

\[
\|x_n-E_{Z(\mathcal A_n)}x_n\|_2^2
=\frac12\int_{\mathcal U(\mathcal A_n)}
\|[x_n,v]\|_2^2\,dv.
\]

If a bounded sequence \((x_n)_\omega\) is central but its
distance from the coordinate centers does not tend to zero along
\(\omega\), select coordinate unitaries witnessing a uniformly
positive commutator norm on an \(\omega\)-large set. Their
ultraproduct contradicts centrality. Conditional expectation keeps
the representatives bounded, proving (38).

Put \(t_i=\lim_\omega t_{n,i}\), where the weights remain sorted
as above, and let \(e_i\) be the ultraproduct of the \(i\)-th
coordinate central atom. If \(t_i>0\), then \(e_i\) is an atom
of the abelian algebra in (38): its coordinate corners are scalar.
These projections are mutually orthogonal.

They are all its atoms. Indeed, suppose an atom \(f\) has trace
\(a>0\) and differs from every nonzero \(e_i\). Then
\(fe_i=0\) for every \(i\). Represent \(f\) by coordinate
central projections \(f_n\), using scalar spectral rounding to
lift projections in the abelian ultraproduct. Choose fixed \(K\)
with \(1/(K+1)<a/4\), and remove the first \(K\) ranked atoms
from \(f_n\), obtaining \(q_n\). Since \(fe_i=0\), this still
represents \(f\), and \(\tau(q_n)\to_\omega a\).
Every remaining coordinate atom has trace at most
\(1/(K+1)<a/4\). On an \(\omega\)-large set
\(\tau(q_n)\geq3a/4\); greedily summing its atoms gives a
subprojection \(g_n\leq q_n\) of trace between \(a/4\) and
\(a/2\). Thus \(0<(g_n)_\omega<f\), contradicting atomicity.

It follows that the total atomic mass of the center is exactly

\[
T=\sum_i\lim_\omega t_{n,i}.
\tag{39}
\]

In particular the center is purely atomic if and only if \(T=1\),
equivalently if and only if the sorted physical weights are tight
along \(\omega\). Combining this characterization with (34)
gives the precise consequence:

\[
\boxed{\begin{gathered}
\|F_nE_n-E_n\|_{\infty\to2}\to_\omega0,
\quad Z(\mathcal A_\omega)\text{ purely atomic}\\
\Longrightarrow\quad
\|E_nF_n-F_n\|_{\infty\to2}\to_\omega0.
\end{gathered}}
\tag{40}
\]

Thus a positive limiting reverse defect forces a nonzero diffuse
part in the center of any such rounded algebra ultraproduct. This
does not assert that the center must be entirely diffuse.

## 10. Scope for the Leavitt compression question

The varying-block example in
[the heat-kernel obstruction artifact](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md)
has \(a_j=2^j\), \(t_j=1/n\), and therefore
\(R=4^{n-1}\). Its vanishing forward error and order-one reverse
error are consistent with (3). The relevant obstruction in that
example includes unbounded dispersion of the trace weights relative
to block dimensions; the presence of a center by itself does not
invalidate reversal.

The canonical finite core of \(H\) provides regular-trace
finite-group algebras in an exact canonical representation. What is
not supplied here is a uniform \(\infty\to2\) approximation of
the native property-\((T)\) heat maps by expectations onto algebras
meeting any of the sufficient reversal conditions: bounded trace
distortion, bounded distortion on a corner of trace tending to one,
a bounded number of central blocks, or tight physical central
weights. Increasing a locally finite core does not by itself give
the required uniform estimate; its commutants can retain directions
in the remaining coordinates.

Under uniform expectation approximation, tight physical central
weights are equivalent to a purely atomic center of the rounded
algebra ultraproduct. This is a condition on that actual range,
not on the group factor generated by the canonical trace. The
[native application](leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md)
uses the forward and reverse heat defects to exclude these rounding
conditions and to force a nonzero diffuse central part if rounding
exists. Neither uniform rounding nor an embedding satisfying the
needed range-center condition is proved here, and the
hyperlinearity verdict remains open.
