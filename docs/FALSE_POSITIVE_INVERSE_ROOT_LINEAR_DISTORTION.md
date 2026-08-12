# The inverse Laurent root has linear positive distortion

Date: 2026-08-12

## 1. Outcome

The inverse-root profile isolated in
FALSE_FROBENIUS_CYCLIC_VECTOR_MIXING_NO_GO.md genuinely diverges in the
actual polynomial/Laurent Kun--Thom pair.

Let

\[
R_+=C[x_1,\ldots ,x_d],\qquad
\Gamma=E_r(R_+)\rtimes Q,
\tag{PIR1}
\]

where \(Q\) acts on the coefficient ring \(C\) and preserves monomial
degree.  Fix any finite generating set \(S\) of \(\Gamma\).  Reduce
coefficients to a nonzero finite quotient \(\bar C\) and impose

\[
x_1^m=\cdots=x_d^m=1.
\tag{PIR2}
\]

Let \(\bar\Gamma_m\) be the resulting finite image.  If \(\bar c\neq0\) in
\(\bar C\), then every \(S\)-word whose image is

\[
e_{ij}(\bar c x_1^{m-1})
=1+\bar c x_1^{m-1}E_{ij}
\tag{PIR3}
\]

has length at least

\[
\frac{m-1}{D_S},
\tag{PIR4}
\]

where \(D_S<\infty\) depends only on the fixed generators and not on \(m\)
or on the coefficient quotient.

For the paired Frobenius fold,

\[
\bar c=\pm\frac12,\qquad x_1^{m-1}=x_1^{-1},
\tag{PIR5}
\]

so the distortion parameter from (FCM35) obeys

\[
\boxed{\lambda_m^-\geq\frac{m-1}{D_S}.}
\tag{PIR6}
\]

Thus exact absorption of the inverse fold necessarily escapes every fixed
positive word ball.  The asymptotic branch cut is intrinsic to the
polynomial-degree filtration.

## 2. Degree growth in a fixed word metric

For a matrix \(g\) over \(R_+\), let

\[
\deg g=\max_{a,b}\deg g_{ab},
\tag{PIR7}
\]

where the degree on the right is total polynomial degree and
\(\deg0=-\infty\).  Matrix multiplication satisfies

\[
\deg(gh)\leq\deg g+\deg h.
\tag{PIR8}
\]

Write an element of the semidirect product (PIR1) as \((g,q)\).  Since
\(Q\) acts only on \(C\), it preserves the degree of every polynomial
entry.  Hence

\[
\deg\bigl(g\,q(h)\bigr)\leq\deg g+\deg h.
\tag{PIR9}
\]

For every \(s\in S\cup S^{-1}\), choose its matrix component \(g_s\), and
put

\[
D_S=\max\left(1,\max_{s\in S\cup S^{-1}}\deg g_s\right).
\tag{PIR10}
\]

Induction using (PIR9) proves:

**Lemma 1 (word-degree bound).**  If \(w\) is an \(S\)-word of length
\(L\), then the matrix component of \(w\) has degree at most \(D_SL\).

This statement is independent of the chosen elementary factorization of a
matrix.  It uses the actual matrix entries of the fixed group generators.

## 3. Reduction modulo the exponent torus

Every class in

\[
\bar B_m=
\bar C[x_1,\ldots,x_d]/(x_1^m-1,\ldots,x_d^m-1)
\tag{PIR11}
\]

has a unique normal form

\[
\sum_{0\leq a_1,\ldots,a_d<m}
c_a x_1^{a_1}\cdots x_d^{a_d}.
\tag{PIR12}
\]

Suppose an \(S\)-word \(w\) of length \(L\) maps to (PIR3).  If
\(D_SL<m-1\), Lemma 1 gives a polynomial lift for the \((i,j)\)-entry of
the matrix component of \(w\) whose total degree is less than \(m-1\).
Its normal form (PIR12) therefore has zero coefficient at
\(x_1^{m-1}\).

The \((i,j)\)-entry of (PIR3) has coefficient \(\bar c\neq0\) at exactly
that monomial.  Uniqueness of (PIR12) gives a contradiction.  Therefore

\[
D_SL\geq m-1,
\tag{PIR13}
\]

which proves (PIR4).

The argument survives square-zero coefficients without change.  The
normal-form monomials are still a \(\bar C\)-basis, and the selected scalar
\(\pm1/2\) is nonzero because the construction uses odd characteristic.

## 4. Consequence for the paired Fourier/Frobenius endpoint

The explicit four-orbit formula (FCM19) propagates positive-label
agreement to the inverse label through elementary roots with coefficient

\[
\pm x_1^{-1}/2.
\tag{PIR14}
\]

At level \(m\), equation (PIR2) identifies (PIR14) with
\(\pm x_1^{m-1}/2\).  Theorem (PIR6) proves that no bounded positive word
can perform this propagation.

Combined with (FCM34)--(FCM36), the surviving quantitative parameter is
therefore the product

\[
\lambda_m^-\eta_m,
\tag{PIR15}
\]

where \(\eta_m\) is the covariance defect of the proposed base-dependent
fiber functor.  Exact or uniformly bounded-depth mixing makes (PIR15)
zero and kills the fold.  A live construction must distribute a total
order-one change across an inverse-root path whose length tends to infinity.

The lower bound (PIR6) does not by itself construct such a path with
sufficiently small local Hilbert--Schmidt cost, nor does it give an upper
bound for \(\lambda_m^-\).  It proves the necessary escape and identifies
the filtration in which a constructive upper bound must be sought.

## 5. Scope

The theorem concerns the common polynomial subgroup \(\Gamma\).  The
external transvection \(t\in L=\operatorname {SL}_d(\mathbb Z)\) sends
\(x_2\) to \(x^{e_2-e_1}\) in one inverse step, but \(t\notin\Gamma\).
Using that external step is precisely the fold being approximated and
cannot be counted as a common positive word.  The linear lower bound is
therefore not bypassed by the ambient Laurent substitution action.
