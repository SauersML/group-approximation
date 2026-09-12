# Heat inclusion for native compression and a finite CP reversal obstruction

2026-09-08. Written finite-dimensional inequalities and counterexample.
No code was run, and no new Lean verification is claimed. This does
not determine hyperlinearity of \(H\).

## 1. Conventions and a finite certified error list

Let \(S\) be a finite symmetric list of literal generating words
of the native \(L=EL_3(R)\), with \(m=|S|\). Pair every word
with its formal inverse and evaluate these pairs as matrices
\(V_s,V_s^*\). Repeated group values are allowed: in particular,
the two spellings of a group involution remain separate list entries.
Thus the averaging operator is exactly self-adjoint even when the
evaluated tuple has nonzero relation defects.
For the native compressor \(u\), choose words \(w_s\) over \(S\)
representing \(usu^{-1}\in L\). Write \(\ell_s=|w_s|\) and

\[
\Lambda=\left(\sum_{s\in S}\ell_s^2\right)^{1/2}.
\]

Use normalized matrix trace and Hilbert--Schmidt norm. On the Hilbert
space \(L^2(M_d)\), let

\[
A=I-\frac1m\sum_{s\in S}\operatorname{Ad}V_s,\qquad
B=\operatorname{Ad}U\,A\,\operatorname{Ad}U^*,\qquad
P_t=e^{-tA},\quad Q_t=e^{-tB}.
\tag{1}
\]

The positive operators \(A,B\) have exactly the same spectrum,
including multiplicities. Both heat maps are unital, trace-preserving,
self-adjoint completely positive contractions. Indeed, if
\(T=I-A\), then
\(P_t=e^{-t}\sum_{j\geq0}t^jT^j/j!\), and every summand is
unital completely positive. In particular heat preserves the
operator unit ball. Also

\[
\mathcal E_A(X):=\langle AX,X\rangle
=\frac1{2m}\sum_s\|\operatorname{Ad}V_s(X)-X\|_2^2.
\]

The finite certified relation list first contains
\(usu^{-1}w_s^{-1}\), with matrix defect at most \(\epsilon\).
For the improved estimate below, also fix one property-\((T)\)
group-algebra SOS identity

\[
\Delta^2-\kappa\Delta=\sum_j\xi_j^*\xi_j,
\qquad \Delta=1-m^{-1}\sum_{s\in S}s,\quad\kappa>0.
\tag{2}
\]

The finite certificate is the one used in
[the adjoint spectral-budget argument](../property-t-hs-adjoint-low-spectrum-budget-proof.md).
Choose words for its finitely many support elements and products;
include the finite kernel rows needed to identify equal words in
the expansion of (2). If each row has defect at most \(\epsilon\),
the adjoint evaluation gives

\[
A^2-\kappa A-\sum_jX_j^*X_j=R_\epsilon,
\qquad
\|R_\epsilon X\|_2\leq C\epsilon\|X\|_{\rm op}.
\tag{3}
\]

Here \(C\) depends only on the fixed expanded certificate. More
explicitly, write its residual as
\(\sum_\nu c_\nu(\operatorname{Ad}W_\nu-
\operatorname{Ad}Z_\nu)\), with the corresponding equality rows
certified. One can take \(C=2\sum_\nu|c_\nu|\), because

\[
\|\operatorname{Ad}W(X)-\operatorname{Ad}Z(X)\|_2
\leq2\|W-Z\|_2\|X\|_{\rm op}.
\]

Equation (3) is an estimate on operator-norm-bounded vectors, not
an operator-norm estimate on all of \(L^2(M_d)\).

## 2. Dimension-independent heat inclusion

Word telescoping and the compressor rows give

\[
\sqrt{\mathcal E_B(X)}
\leq\Lambda\sqrt{\mathcal E_A(X)}
       +\sqrt2\epsilon\|X\|_{\rm op}.
\tag{4}
\]

For details, put \(a_s=\|\operatorname{Ad}V_s(X)-X\|_2\).
The commutator for \(w_s\) is bounded by the sum of its
\(\ell_s\) letter commutators, hence by
\(\ell_s(\sum_t a_t^2)^{1/2}\). Sum the squares over \(s\)
and divide by \(2m\). The direct compressor error contributes
at most \(2\epsilon\|X\|_{\rm op}\) to each commutator;
Minkowski gives (4).

Spectral calculus gives
\(\mathcal E_A(P_tY)\leq\|Y\|_2^2/(2et)\), using
\(\sup_{\lambda\geq0}\lambda e^{-2t\lambda}=1/(2et)\).
The scalar inequality \((1-e^{-s\lambda})^2\leq s\lambda\)
then proves, for every \(s,t>0\),

\[
\boxed{
\|Q_sP_tY-P_tY\|_2
\leq\Lambda\sqrt{\frac{s}{2et}}\|Y\|_2
       +\sqrt{2s}\epsilon\|Y\|_{\rm op}.}
\tag{5}
\]

This estimate needs only the compressor rows, not (2).

## 3. The SOS certificate permits the same heat time

Let \(Y_t=P_tY\), and set \(g(t)=\mathcal E_A(Y_t)\).
The heat contraction and (3) imply

\[
\langle A^2Y_t,Y_t\rangle
\geq\kappa g(t)-C\epsilon\|Y\|_{\rm op}^2.
\]

Since \(g'(t)=-2\langle A^2Y_t,Y_t\rangle\) and
\(0\leq A\leq2I\), differential comparison gives

\[
g(t)\leq2e^{-2\kappa t}\|Y\|_2^2
           +\frac{C\epsilon}{\kappa}\|Y\|_{\rm op}^2.
\tag{6}
\]

Combining (4), (6), and the same scalar heat inequality yields

\[
\boxed{
\|Q_tP_tY-P_tY\|_2
\leq\Lambda\sqrt{2t}e^{-\kappa t}\|Y\|_2
 +\left(\Lambda\sqrt{\frac{Ct\epsilon}{\kappa}}
           +\sqrt{2t}\epsilon\right)\|Y\|_{\rm op}.}
\tag{7}
\]

The same argument with \(B=A\), without compressor error, gives
approximate idempotence:

\[
\|P_t^2Y-P_tY\|_2
\leq\sqrt{2t}e^{-\kappa t}\|Y\|_2
        +\sqrt{\frac{Ct\epsilon}{\kappa}}\|Y\|_{\rm op}.
\tag{8}
\]

Conjugation gives (8) for \(Q_t\) as well. For
\(t=\kappa^{-1}\log(1/\epsilon)\), with \(0<\epsilon<1\),
both (7) and (8) are \(O(\sqrt{\epsilon\log(1/\epsilon)})\)
uniformly on the operator unit ball. Thus positivity and heat
regularization do supply a uniformly controlled one-sided inclusion.
The following finite example shows why this statement cannot simply
be reversed using equality of spectra.

### The heat maps recover the full ultraproduct commutant

Retaining the initial energy instead of bounding it by
\(2\|X\|_2^2\), the same differential inequality gives

\[
\mathcal E_A(P_sX)
\leq e^{-2\kappa s}\mathcal E_A(X)
       +\frac{C\epsilon}{\kappa}\|X\|_{\rm op}^2.
\]

Since \(0\leq P_t\leq I\) as Hilbert-space operators,

\[
\begin{aligned}
\|P_tX-X\|_2^2
&\leq\|X\|_2^2-\|P_tX\|_2^2
=2\int_0^t\mathcal E_A(P_sX)\,ds\\
&\leq\frac{\mathcal E_A(X)}{\kappa}
      +\frac{2C\epsilon t}{\kappa}\|X\|_{\rm op}^2.
\end{aligned}
\tag{8a}
\]

Consider full asymptotic representations in a tracial matrix
ultraproduct \(\mathcal M\), with \(\epsilon_n\to0\),
\(t_n\to\infty\), and \(\epsilon_nt_n\to0\). The maps
\(P_{t_n}\) induce a well-defined self-adjoint bistochastic CP
map \(\mathcal P\) on \(\mathcal M\), since they contract
\(L^2\) and operator norm. By (6), every bounded output sequence
asymptotically commutes with the generators of \(L\). Hence the
range lies in \(\pi(L)'\cap\mathcal M\).

Conversely, a bounded sequence representing an element of that
commutant has initial energy tending to zero. Equation (8a) shows
that \(P_{t_n}\) fixes it in the ultraproduct, without any extra
assumption on the rate of its generator commutators. Therefore

\[
\mathcal P=E_{\pi(L)'\cap\mathcal M}.
\tag{8b}
\]

This identifies the limiting expectation. It does not lift its
range to a sequence of finite-dimensional matrix subalgebras.

## 4. Exact conditional expectations with one-sided but not reverse inclusion

For \(n\geq2\), let \(d=n2^n\), and split \(\mathbb C^d\)
into \(n\) equal blocks \(\mathcal H_j=(\mathbb C^2)^{\otimes n}\),
\(0\leq j<n\). In \(M_d\), put

\[
\mathcal A_n=
\bigoplus_{j=0}^{n-1}
\left(M_{2^j}\otimes I_{2^{n-j}}\right).
\tag{9}
\]

Let \(U\) cyclically permute the blocks so that
\(\mathcal B_n=U\mathcal A_nU^*\) has block algebra
\(M_{2^{j+1}}\otimes I\) when \(j<n-1\), and has scalar
algebra in its last block. Take the trace-preserving conditional
expectations

\[
P=E_{\mathcal A_n},\qquad Q=E_{\mathcal B_n}.
\]

These maps are exactly idempotent, self-adjoint, trace-preserving,
unital completely positive, and unitarily conjugate. Their spectra
and ranks agree. They also commute: within each block one algebra
contains the other, and both expectations annihilate off-diagonal
blocks. The inclusion \(\mathcal A_j\subset\mathcal B_j\)
fails only on the last block, of physical trace \(1/n\).
Consequently

\[
\|QP-P\|_{\infty\to2}=n^{-1/2}.
\tag{10}
\]

For the upper bound, the difference is the orthogonal projection
onto the traceless part of \(\mathcal A_{n-1}\), supported on
the last block. Its norm on a contraction is at most \(1/\sqrt n\).
A traceless unitary in that block attains the bound.

Let \(Z=\operatorname{diag}(1,-1)\). Define a unitary \(X\)
whose block \(j<n-1\) is

\[
I_{2^j}\otimes Z\otimes I_{2^{n-j-1}},
\]

and whose last block is the identity. Then \(QX=X\), whereas
\(PX=0\) on the first \(n-1\) blocks and equals the identity
on the last block. Therefore

\[
\boxed{\quad
\|PQX-QX\|_2=\sqrt{1-1/n}.\quad}
\tag{11}
\]

Thus uniform one-sided inclusion on the whole operator unit ball,
even with exact positivity, idempotence, conjugacy, and equal
spectra, does not imply reverse inclusion on unitary vectors.

This example also satisfies the energy comparison underlying (4)
with constants independent of \(n\). Set \(A=I-P\), \(B=I-Q\).
The positive part of \(P-Q\) is supported on the last block, so

\[
\mathcal E_B(Y)\leq\mathcal E_A(Y)+n^{-1}\|Y\|_{\rm op}^2,
\qquad
\sqrt{\mathcal E_B(Y)}
\leq\sqrt{\mathcal E_A(Y)}+n^{-1/2}\|Y\|_{\rm op}.
\]

Thus the analytic energy comparison itself, even with exact gap one,
does not prevent the counterexample. This does not assert a realization
of its averaging groups by the fixed native compressor words.

The rank bookkeeping is explicit. The new bulk dimensions total
\(4^{n-1}-1\), exactly the dimensions lost on the last block.
That block has trace \(1/n\); a normalized \(L^2\)-unit vector
supported there has operator norm at least \(\sqrt n\).
Also

\[
\frac{\dim\mathcal A_n}{d^2}
=\frac{4^n-1}{3n^2 4^n}\longrightarrow0.
\]

The low-rank operator space can nevertheless contain the unitary
\(X\) from (11), which has a macroscopic reverse defect.

## 5. Heat maps and commuting complementary algebras in the same example

The positive Laplacians \(I-P,I-Q\) have the exact gap one.
They can also be written as adjoint averaging Laplacians of finite
unitary groups: average over blockwise finite Pauli groups generating
\(\mathcal A_n'\), together with independent block scalar signs
that remove off-diagonal blocks. The common commutant is exactly
\(\mathcal A_n\), so this group average is \(P\). Conjugate the
finite group by \(U\) for \(Q\). These finite groups depend on
\(n\); they are not fixed native generators for \(H\).
Their heat maps are

\[
\widetilde P_t=P+e^{-t}(I-P),\qquad
\widetilde Q_t=Q+e^{-t}(I-Q).
\]

They retain exact unitary conjugacy and satisfy

\[
\|\widetilde Q_t\widetilde P_t-\widetilde P_t\|_{\infty\to2}
\leq n^{-1/2}+e^{-t},
\qquad
\|\widetilde P_t\widetilde Q_tX-\widetilde Q_tX\|_2
=(1-e^{-t})\sqrt{1-1/n}.
\tag{12}
\]

The commutant algebras also give a simultaneous complementary pair:
\(\mathcal A_n'\) has block algebra
\(I_{2^j}\otimes M_{2^{n-j}}\), and
\(\mathcal B_n'=U\mathcal A_n'U^*\). Their inclusions run in
the reverse direction on the first \(n-1\) blocks, with only
the last block exceptional. The two expectations for
\(\mathcal A_n,\mathcal A_n'\) commute, and their product is
the expectation onto block scalars; the conjugated pair has exactly
the same product. The witness \(X\) lies in
\(\mathcal B_n\cap\mathcal A_n'\), so it has the location of
the native compressed-centralizer witness.

This is a counterexample to the proposed CP/spectral inference,
not a tuple satisfying the full presentation of \(H\). No claim
is made that these block algebras arise from the two native copies
with all their prescribed relations or canonical joint word traces.
For example, the block height \(F_n|_{\mathcal H_j}=j/n\) commutes
with both original algebras, has asymptotic variance \(1/12\),
and satisfies \(\|[U,F_n]\|_2=\sqrt{n-1}/n\to0\).
The example therefore contains an explicit slowly varying global
commutant direction. Eliminating the example for the native tuples
would require additional H-specific information; properties
(7)--(8), exact equal spectra, and the complementary CP structure
alone do not eliminate it.
