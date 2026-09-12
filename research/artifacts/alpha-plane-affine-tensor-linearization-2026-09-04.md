# Affine tensor amplification linearizes the matrix alpha-plane modulus

Date: 2026-09-04. Status: a complete proof of the implication from the
existing qualitative theorem to the linear inequality. This note does not
independently reprove the qualitative theorem's Loeb/probability-algebra
argument, supply a numerical stability threshold, or prove nonhyperlinearity.

## Statement

Let K be a finite field of characteristic two, q=|K|>=4, and let alpha
generate K over F_2. Write tau_d=Tr/d and ||X||_2^2=tau_d(X*X).
All averages below are uniform. For any table R:K->U(d), define

\[
D_b(x)=R_{x+b}R_x^*,\qquad
E_t(R)=\mathbb E_{x,b}\|D_b(x)-D_b(x+tb)\|_2^2,
\]
\[
I(R)=E_1(R),\quad A(R)=E_\alpha(R),\quad
F(R)=\mathbb E_{x,a,b}\|D_b(x)-D_b(x+a)\|_2^2.
\]

The identity I=E_1 uses characteristic two and agrees exactly with (NC1)
in `matrix-phase-noncommutative-alpha-plane-route`.

**Theorem.** Suppose there is epsilon_*>0, uniform over these fields,
alphas, and matrix dimensions, such that

\[
I(R)+A(R)\le\varepsilon_*
\quad\Longrightarrow\quad F(R)\le\tfrac14. \tag{1}
\]

Then every such table satisfies

\[
F(R)\le\frac{I(R)+A(R)}{\varepsilon_*}. \tag{2}
\]

Consequently a uniform vanishing qualitative modulus and a uniform linear
bound are equivalent. The archive's qualitative theorem (NC25), if accepted,
provides the premise (1), so no additional analytic stability hypothesis is
needed for the existence of the linear constant. Computing epsilon_* remains
a different task.

## 1. A bound on every slope

For a fixed b, put M_b=E_x D_b(x) and
V_b=E_x ||D_b(x)-M_b||_2^2. Hilbert-space variance gives

\[
\mathbb E_{x,a}\|D_b(x)-D_b(x+a)\|_2^2=2V_b.
\]

Since D_b(x) is unitary, V_b=1-||M_b||_2^2<=1. In particular

\[
0\le F(R)=2\mathbb E_b V_b\le2. \tag{3}
\]

For each fixed t, translation by tb preserves the uniform x-average, so

\[
\mathbb E_x\|D_b(x)-D_b(x+tb)\|_2^2
\le 2\mathbb E_x\|D_b(x)-M_b\|_2^2
+2\mathbb E_x\|D_b(x+tb)-M_b\|_2^2=4V_b.
\]

Therefore

\[
0\le E_t(R)\le2F(R)\quad\text{for every }t\in K. \tag{4}
\]

Also b=0 contributes zero, and for b!=0 the map t->tb is a bijection of K.
Thus

\[
\mathbb E_t E_t(R)=F(R). \tag{5}
\]

Estimate (4) prevents the full energy from hiding on an arbitrarily small
set of slopes. It is the point missing from a naive application of tensor
powers to an averaged target.

## 2. Real traces and affine symmetrization

First replace R_x by R_x plus its entrywise complex conjugate in block
diagonal sum. All energies are unchanged. For every word W in the table and
its adjoints, the new normalized trace of W is Re tau_d(W). In particular,
all the quartic correlations below become real.

Let Aff(K)={g(x)=ux+v: u in K^*, v in K}. For any real-trace table B form

\[
S_x=\bigoplus_{g\in\operatorname{Aff}(K)}B_{g(x)}.
\]

The equal-size blocks give the uniform average over g in every normalized
trace. Fix x, b!=0, and t. Under uniform g, (g(x),ub) is uniform on
K times K^*. The four points x,x+b,x+tb,x+(t+1)b become the same slope-t
configuration at this uniform basepoint and nonzero direction. With
beta=1-1/q, it follows that

\[
\tau\big(D_b^S(x)D_b^S(x+tb)^*\big)
=1-\frac{E_t(B)}{2\beta}=:c_t. \tag{6}
\]

This equality is pointwise in x and b!=0, including the repeated-point
slopes t=0 and t=1. No freeness of a four-point orbit is being assumed.

## 3. Exact tensor formulas

For an integer k>=1 set T_x=S_x^{\otimes k}. Word evaluation commutes with
tensor products, and normalized traces multiply. From (6),

\[
E_t(T)=2\beta\left[1-
\left(1-\frac{E_t(B)}{2\beta}\right)^k\right], \tag{7}
\]
\[
F(T)=2\beta\mathbb E_t\left[1-
\left(1-\frac{E_t(B)}{2\beta}\right)^k\right]. \tag{8}
\]

The order of operations matters: affine symmetrization precedes tensoring.
Tensoring the original table does not replace an average correlation by its
k-th power.

## 4. Amplify any violation of the proposed linear bound

Take R with f_0=F(R)>0 and delta_0=I(R)+A(R). Set m=2q, dilute by
identity blocks, and then make traces real:

\[
Q_x=R_x\oplus I_{(m-1)d},\qquad B_x=Q_x\oplus\overline{Q_x}.
\]

Every energy is divided by m, so f=F(B)=f_0/m and
delta=I(B)+A(B)=delta_0/m. By (3),

\[
0<f\le1/q\le\beta.
\]

Write e_t=E_t(B)/(2beta). Equations (4)--(5) give

\[
0\le e_t\le f/\beta\le1,\qquad
\mathbb E_t e_t=f/(2\beta). \tag{9}
\]

Choose k=ceil(beta/f) and apply Sections 2--3 to B. Bernoulli's inequality
1-(1-e)^k<=ke on [0,1] gives

\[
I(T)+A(T)\le k\delta
=kf\,\frac{\delta_0}{f_0}
\le(\beta+f)\frac{\delta_0}{f_0}
\le\frac{\delta_0}{f_0}. \tag{10}
\]

For the reverse bound on F, the function phi(e)=1-(1-e)^k is concave and
phi(0)=0. Its chord on [0,f/beta] lies below its graph. Hence (9) gives

\[
\mathbb E_t\phi(e_t)
\ge\frac{\mathbb E_t e_t}{f/\beta}\phi(f/\beta)
=\tfrac12\phi(f/\beta).
\]

Using kf/beta>=1 and 1-z<=exp(-z),

\[
F(T)\ge\beta[1-(1-f/\beta)^k]
\ge\beta(1-e^{-1})
\ge\tfrac34(1-e^{-1})>\tfrac14. \tag{11}
\]

If delta_0/f_0<=epsilon_*, (10) meets the hypothesis of (1), while (11)
contradicts its conclusion. Thus every table with f_0>0 has
delta_0/f_0>epsilon_*, which implies (2). The f_0=0 case is immediate.
All constructed dimensions are finite; they may be enormous, which is
permitted precisely because (1) is uniform in dimension. This proves the
theorem.

## 5. Exact additive actions reduce to the same table

There is also a direct reduction with no choice of orbit blocks. Let
X,Z:(K,+)->U(d) be exact representations, with no assumed commutation
between their images. Set R_x=X(x)Z(x). Since every element of K has
additive order at most two,

\[
D_b(x)=X(x)X(b)Z(b)X(x)^*.
\]

For every x,a,b, bi-invariance of the norm and commutation within X give

\[
\|D_b(x)-D_b(x+a)\|_2
=\|X(a)Z(b)-Z(b)X(a)\|_2. \tag{12}
\]

Therefore the theorem gives the untwisted two-matching inequality

\[
\mathbb E_{a,b}\|[X(a),Z(b)]\|_2^2
\le C\mathbb E_b\left(
\|[X(b),Z(b)]\|_2^2+
\|[X(\alpha b),Z(b)]\|_2^2\right), \tag{13}
\]

where [A,B] in (13) denotes AB-BA. This requires exact additive actions
on one Hilbert space before the estimate is applied. It is not an
exactification theorem for locally named occurrences. Twisted Weyl
commutation would require a separate untwisting reduction; (13) does not
silently identify the twisted and untwisted assertions.

## What this changes, and what it does not

The claim `matrix-phase-linear-alpha-plane-inequality` is a consequence of
`matrix-phase-noncommutative-alpha-plane-route`. That consequence uses no
quantitative simultaneous diagonalization, polar-correction contraction,
Poincare--Lojasiewicz inequality, or multiplicative-cycle spectral gap.

The dependence on the qualitative theorem is explicit and essential to the
application. A separate proof route for that theorem is
`matrix-phase-polar-consensus-compactness-proof`, requiring the scalar
alpha-plane theorem, so the existing reverse implication from linear to
qualitative need not be used and creates no circular proof here.

This proves the existence of a universal C. It gives C=1/epsilon_* in
terms of a coarse stability threshold but does not calculate that threshold.
The arbitrary-unitary table inequality also does not manufacture the coherent
table/carrier required in the nonhyperlinear-group routes.

## Prior art and novelty boundary

Tensor amplification itself is classical and already appears in this
repository's `character-domination-collapse-equivalences` and
`sofic-radical-linear-action-proof`. A general exposition is Terence Tao,
[Amplification, arbitrage, and the tensor power trick](https://terrytao.wordpress.com/2007/09/05/amplification-arbitrage-and-the-tensor-power-trick/)
(2007). The contribution claimed here is the specific slope estimate (4)
combined with Aff(K)-symmetrization to linearize this averaged matrix
alpha-plane test. A targeted repository and web search on 2026-09-04 did
not locate this application; that search is not proof of global novelty.

The scalar input used by the archive is Kaufman--Sudan,
[Algebraic Property Testing: The Role of Invariance](https://www.ias.edu/sites/default/files/math/csdm/06-07/tkaufman_algebraic_property_testing.pdf).
That scalar theorem is prior work, not a result of this note.

The proof above is written mathematics, not a Lean-checked theorem.
