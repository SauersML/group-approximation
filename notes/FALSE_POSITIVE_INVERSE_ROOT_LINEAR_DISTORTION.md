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

There is also a uniform polynomial upper bound.  If \(\kappa_S>0\) is a
Kazhdan constant for \((\Gamma,S)\), then

\[
\lambda_m^-
\leq C_S\left(r^2m^d\log|\bar C|+\log|\bar Q|+1\right),
\tag{PIR6a}
\]

where \(\bar Q\) is the coefficient-group image and
\(C_S=4|S|/\kappa_S^2+1\) is sufficient.  Thus the inverse-root distortion
is bracketed between a linear lower bound and a volume-polynomial upper
bound.

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

## 4. Property (T) gives a polynomial upper bound

We record the standard quantitative diameter consequence in the normalization
needed here.

**Lemma 2 (Kazhdan diameter bound).**  Let a group
\(\Lambda=\langle S\rangle\) have Kazhdan constant \(\kappa_S>0\), with
\(S=S^{-1}\) finite.  Every finite quotient \(K\) of \(\Lambda\) satisfies

\[
\operatorname {diam}(K,\bar S)
\leq
\left(\frac{4|S|}{\kappa_S^2}+1\right)(\log|K|+1).
\tag{PIR13a}
\]

**Proof.**  On the orthogonal complement of the constants in
\(\ell^2(K)\), put

\[
P=\frac1{|S|}\sum_{s\in S}\lambda(s).
\tag{PIR13b}
\]

For every unit vector \(\xi\) in that subspace, the Kazhdan inequality gives

\[
2\langle(1-P)\xi,\xi\rangle
=\frac1{|S|}\sum_{s\in S}\|\lambda(s)\xi-\xi\|^2
\geq\frac{\kappa_S^2}{|S|}.
\tag{PIR13c}
\]

The lazy operator \(M=(1+P)/2\) is positive and therefore has norm at most
\(1-\kappa_S^2/(4|S|)\) on the same subspace.  Starting at a point mass,
after \(k\) lazy steps its distance from the uniform distribution is at
most

\[
\left(1-\frac{\kappa_S^2}{4|S|}\right)^k.
\tag{PIR13d}
\]

For \(k>(4|S|/\kappa_S^2)(\log|K|+1)\), this is less than \(1/|K|\).
Every coordinate of the probability distribution is then positive, so
the radius-\(k\) word ball is all of \(K\).  This proves (PIR13a).  End
proof.

The finite image in the present construction embeds in

\[
\operatorname {GL}_r(\bar B_m)\rtimes\bar Q.
\tag{PIR13e}
\]

Since \(|\bar B_m|=|\bar C|^{m^d}\),

\[
\log|\bar\Gamma_m|
\leq r^2m^d\log|\bar C|+\log|\bar Q|.
\tag{PIR13f}
\]

The inverse root (PIR3) belongs to \(\bar\Gamma_m\), because the positive
coefficient map surjects onto \(\bar B_m\).  Lemma 2 and (PIR13f) prove
(PIR6a).

For the standard square-zero coefficient quotient
\[
\bar C=(\mathbb Z/p^n\mathbb Z)
\ltimes(\mathbb Z/p^n\mathbb Z)^3,
\qquad
\bar Q=\operatorname {SL}_3(\mathbb Z/p^n\mathbb Z),
\tag{PIR13g}
\]
one obtains the concrete coarse window

\[
\frac{m-1}{D_S}
\leq\lambda_{m,n}^-
\leq C_{S,r,p}\,(nm^d+n+1).
\tag{PIR13h}
\]

No claim of sharpness is made for the upper exponent \(d\).  Its value is
that the constructive rate problem is polynomially bounded in the actual
finite parameters.

## 5. Consequence for the paired Fourier/Frobenius endpoint

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

The degree lower bound (PIR6) does not by itself construct such a path with
sufficiently small local Hilbert--Schmidt cost.  Lemma 2 supplies a coarse
word-metric upper bound, but not a coherent path of polarizations attaining
the required covariance estimate.  Together they identify the finite
polynomial window in which that construction must be sought.

## 6. Scope

The theorem concerns the common polynomial subgroup \(\Gamma\).  The
external transvection \(t\in L=\operatorname {SL}_d(\mathbb Z)\) sends
\(x_2\) to \(x^{e_2-e_1}\) in one inverse step, but \(t\notin\Gamma\).
Using that external step is precisely the fold being approximated and
cannot be counted as a common positive word.  The linear lower bound is
therefore not bypassed by the ambient Laurent substitution action.
