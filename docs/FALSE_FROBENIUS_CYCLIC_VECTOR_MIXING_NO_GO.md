# Cyclic Frobenius labels force exact copy mixing to absorb the fold

Date: 2026-08-12

## 1. Outcome

The finite Frobenius tangent model has a stronger exact-absorption property
than was previously recorded.  Let \(A\) be a finite commutative ring in
which \(2\) is invertible, let \(B\) be a commutative \(A\)-algebra, and let


\[
E=\mathfrak {sl}_r(B),\qquad H=E_r(B),
\tag{FCM1}
\]

where \(r\geq4\) is even.  Put

\[
P=\operatorname {diag}(1,-1,1,-1,\ldots ,1,-1).
\tag{FCM2}
\]

For every unit \(b\in B^\times\), the vector \(bP\) is cyclic for the
adjoint \(H\)-action on \(E\):

\[
A[H](bP)=E.
\tag{FCM3}
\]

In the Laurent specialization, the common positive tangent label is

\[
z_+=P x_2\otimes a,
\tag{FCM4}
\]

while the inverse-fold label is

\[
z_-=P x^{e_2-e_1}\otimes a.
\tag{FCM5}
\]

There is an explicit expression of \(z_-\) as a sum of only \(2r\) signed
\(H\)-translates of \(z_+\).  The number of translates is independent of the
finite quotient.  The only quantity which can grow is the **positive word
length** of an elementary root with coefficient

\[
\frac{x^{e_2-e_1}}{x_2}=x_1^{-1}.
\tag{FCM6}
\]

Consequently, any exact \(A\)-linear, base-equivariant copy-mixing map that
aligns the two sectors on \(z_+\) aligns them on the entire tangent module,
and in particular on \(z_-\).  A successful paired Fourier/Frobenius
construction therefore cannot be obtained by tensoring the local cells and
then applying one exact global linear mixing in the commutant of the base
action.

For an arbitrary approximately covariant system, the direct quantitative
estimate pays the transport length. If \(\eta_n\) is the base-covariance
defect and \(\lambda_n^-\) is the positive word length of the root in
`(FCM6)`, then the marked discrepancy is bounded by

\[
O_r\bigl(\epsilon_n+(1+\lambda_n^-)\eta_n\bigr),
\tag{FCM7}
\]

where \(\epsilon_n\) is the discrepancy on \(z_+\). Thus the elementary
telescoping estimate alone says that a macroscopic fold with
\(\epsilon_n,\eta_n\to0\) requires

\[
\lambda_n^-\eta_n\not\longrightarrow0.
\tag{FCM8}
\]

This apparent rate escape is **not available** when the base matrices are
exact representations of a fixed property-`(T)` group and tangent
covariance is exact. The Kazhdan bimodule projection theorem in
`FALSE_KAZHDAN_CYCLIC_SEED_PROPAGATION_NO_GO.md` improves `(FCM7)` in that
regime to

\[
 2r\epsilon_n+\frac{4r+2}{\kappa}\eta_n,
 \tag{FCM8a}
\]

with no factor \(\lambda_n^-\). Consequently the live construction must put
genuine normalized-Hilbert--Schmidt nonliftability into the base map or the
tangent covariance itself; a long branch cut inside an exact Kazhdan
covariant pair cannot retain the fold.

## 2. The alternating diagonal is an adjoint cyclic vector

Write \(p_i\in\{1,-1\}\) for the \(i\)-th diagonal entry of \(P\).  Let

\[
\mathcal U=\operatorname {span}_A
 \{\operatorname {Ad}(h)(bP):h\in H\}\subseteq E.
\tag{FCM9}
\]

It is an \(H\)-invariant \(A\)-submodule.  If \(i\neq j\) have opposite
parity and \(u\in B\), then \(E_{ij}^2=0\) and direct multiplication gives

\[
\operatorname {Ad}(1+uE_{ij})(bP)-bP
   =bu(p_j-p_i)E_{ij}.
\tag{FCM10}
\]

The scalar \(b(p_j-p_i)=\pm2b\) is a unit.  As \(u\) varies, `(FCM10)` shows

\[
BE_{ij}\subseteq\mathcal U
\quad\text{whenever \(i,j\) have opposite parity.}
\tag{FCM11}
\]

Now let \(i,k\) have the same parity and choose \(j\) of the opposite
parity.  The three indices are distinct, and

\[
\operatorname {Ad}(1+vE_{jk})(cE_{ij})-cE_{ij}
  =-cvE_{ik}.
\tag{FCM12}
\]

Taking \(c=1\) and arbitrary \(v\in B\) gives every same-parity root space.
Together with `(FCM11)`, this proves

\[
BE_{ij}\subseteq\mathcal U\qquad(i\neq j).
\tag{FCM13}
\]

Finally, for \(i\neq j\),

\[
\operatorname {Ad}(1+E_{ji})(cE_{ij})-cE_{ij}
 =c(E_{jj}-E_{ii})-cE_{ji}.
\tag{FCM14}
\]

The off-diagonal term belongs to \(\mathcal U\) by `(FCM13)`.  Hence every
\(c(E_{ii}-E_{jj})\) belongs to \(\mathcal U\).  The root matrices and these
diagonal differences span \(\mathfrak {sl}_r(B)\), so `(FCM3)` follows.

This proof needs no field hypothesis, semisimplicity, or classification of
the adjoint commutant.  Invertibility of \(2b\) is the only division used.

If \(V=A^d\), \(d\geq2\), and \(Q=\operatorname {SL}_d(A)\) acts in the
standard way, then \(a=e_1\) is cyclic in \(V\):

\[
(1+tE_{j1})a-a=te_j.
\tag{FCM15}
\]

It follows from `(FCM3)` and `(FCM15)` that

\[
bP\otimes a
\quad\text{is cyclic in}\quad
E\otimes_A V
\tag{FCM16}
\]

for the product action of \(H\times Q\).  The narrower \(H\)-cyclicity in
`(FCM3)` already suffices for the two Laurent labels `(FCM4)--(FCM5)`.

## 3. An explicit four-orbit formula

The cyclicity proof can be sharpened to a constant-size identity.  Let
\(i,j\) have opposite parity, with \(p_i=1\) and \(p_j=-1\), and let
\(d\in B\).  Define

\[
u=-\frac{d}{2b},\qquad v=\frac{d}{2b},
\quad e=1+uE_{ij},\quad f=1+E_{ji},\quad e'=1+vE_{ji}.
\tag{FCM17}
\]

Equation `(FCM10)` gives

\[
\operatorname {Ad}(e)(bP)-bP=dE_{ij},
\qquad
\operatorname {Ad}(e')(bP)-bP=dE_{ji}.
\tag{FCM18}
\]

Substitute these identities into `(FCM14)`.  The two copies of \(bP\)
cancel, leaving

\[
\boxed{
d(E_{ii}-E_{jj})
=\operatorname {Ad}(e)(bP)
-\operatorname {Ad}(fe)(bP)
+\operatorname {Ad}(f)(bP)
-\operatorname {Ad}(e')(bP).}
\tag{FCM19}
\]

Pair the coordinates of `(FCM2)` as
\((1,2),(3,4),\ldots,(r-1,r)\) and sum `(FCM19)`.  This expresses \(dP\)
as \(4(r/2)=2r\) signed orbit vectors.

For `(FCM4)--(FCM5)`, take

\[
b=x_2,\qquad d=x^{e_2-e_1},
\tag{FCM20}
\]

so that

\[
u=-\frac{x_1^{-1}}2,qquad v=\frac{x_1^{-1}}2.
\tag{FCM21}
\]

This identifies the inverse coefficient, rather than the size of the clock
or the dimension of the Frobenius module, as the unique growing datum in
the exact propagation formula.

## 4. Exact copy-mixing no-go

Let a group \(F\) act \(A\)-linearly on an \(A\)-module \(W\), and suppose
\(z\in W\) is cyclic:

\[
A[F]z=W.
\tag{FCM22}
\]

For \(\alpha=(\alpha_1,\ldots,\alpha_m)\in A^m\), write

\[
\iota_\alpha(w)=(\alpha_1w,\ldots,\alpha_mw)\in W^m.
\tag{FCM23}
\]

**Theorem 1 (exact cyclic mixing obstruction).**  Let
\(T:W^m\to W^m\) be \(A\)-linear and \(F\)-equivariant.  If

\[
T\iota_\beta(z)=\iota_\alpha(z),
\tag{FCM24}
\]

then

\[
T\iota_\beta(w)=\iota_\alpha(w)
\qquad\text{for every }w\in W.
\tag{FCM25}
\]

**Proof.**  The map

\[
D=T\iota_\beta-\iota_\alpha:W\longrightarrow W^m
\tag{FCM26}
\]

is \(A\)-linear and \(F\)-equivariant.  Equation `(FCM24)` says \(D(z)=0\).
Therefore \(D\) vanishes on \(A[F]z=W\).  This is `(FCM25)`.  End proof.

Apply this with \(W=E\otimes_A V\), \(F=H\times Q\), and \(z=z_+\).
Equations `(FCM3)--(FCM16)` show that the hypothesis `(FCM22)` holds.
Thus every exact global linear copy mixer which is equivariant for the full
finite base action and aligns the common positive tangent label also aligns
the inverse-fold label \(z_-\).  It cannot retain the marked energy.

The same argument applies to a relative-holonomy intertwiner.  If a unitary
\(U\) intertwines two exact additive \(F\)-covariant representations on the
single cyclic label \(z_+\), then equivariance and additivity propagate the
intertwining to every label.  Nontrivial holonomy cannot hide in the exact
commutant of the base action.

## 5. Quantitative propagation and the branch-cut cost

The asymptotic construction escapes Theorem 1 only because the element
with coefficient \(x_1^{-1}\) is represented by a positive word whose
length grows with the finite quotient.  The following elementary estimate
makes that statement exact.

Let \(F=\langle S\rangle\) act on a finite abelian group \(W\), where
\(S=S^{-1}\) is finite and symmetric.  Let

\[
\Phi_0,\Phi_1:W\longrightarrow\mathcal U(N)
\tag{FCM27}
\]

be homomorphisms of additive groups.  Suppose one common family of unitaries
\(U_s\), \(s\in S\), has covariance defect at most \(\eta\) on every label
encountered below:

\[
\|U_s\Phi_i(w)U_s^*-\Phi_i(sw)\|_2\leq\eta
\qquad(i=0,1).
\tag{FCM28}
\]

Put

\[
\epsilon=\|\Phi_0(z)-\Phi_1(z)\|_2.
\tag{FCM29}
\]

If \(g\in F\) has \(S\)-length \(\ell_S(g)\), telescoping `(FCM28)` gives

\[
\|\Phi_0(gz)-\Phi_1(gz)\|_2
\leq\epsilon+2\ell_S(g)\eta.
\tag{FCM30}
\]

If

\[
w=\sum_{\nu=1}^k n_\nu g_\nu z
\quad\text{in }W,
\qquad n_\nu\in\mathbb Z,
\tag{FCM31}
\]

then additivity of the \(\Phi_i\), followed by the usual telescoping estimate
for products of unitaries, yields

\[
\|\Phi_0(w)-\Phi_1(w)\|_2
\leq
\sum_{\nu=1}^k|n_\nu|
 \bigl(\epsilon+2\ell_S(g_\nu)\eta\bigr).
\tag{FCM32}
\]

Define the orbit-filling cost

\[
\mathfrak c_S(w;z)=
\min_{(\mathrm{FCM31})}
\sum_{\nu=1}^k|n_\nu|
 \bigl(1+\ell_S(g_\nu)\bigr).
\tag{FCM33}
\]

Then `(FCM32)` implies

\[
\|\Phi_0(w)-\Phi_1(w)\|_2
\leq2\mathfrak c_S(w;z)\max\{\epsilon,\eta\}.
\tag{FCM34}
\]

For the explicit identity `(FCM19)`, assume the positive finite image
contains the relevant elementary roots and that each \(1+E_{ji}\) is a
chosen generator.  If

\[
\lambda^-(d/b)=
\max_{i,j}
\left\{
 \ell_S\left(1-\frac{d}{2b}E_{ij}\right),
 \ell_S\left(1+\frac{d}{2b}E_{ji}\right)
\right\},
\tag{FCM35}
\]

then the four terms in `(FCM19)` give

\[
\mathfrak c_S(dP;bP)
\leq\frac{3r}{2}\bigl(\lambda^-(d/b)+2\bigr).
\tag{FCM36}
\]

The harmless numerical constant is not important; the dependence on only
one inverse-root distortion is.  Combining `(FCM34)` and `(FCM36)` gives
`(FCM7)--(FCM8)`.

## 6. Consequence for the surviving FALSE route

The theorem closes the following tempting completion:

1. take many exact long Fourier/Frobenius cells;
2. tensor or sum them over a finite principal bundle;
3. use one exact base-equivariant linear transformation of the copy index to
   cancel all external monodromy; and
4. retain the inverse fold in the orthogonal complement.

Step 3 is incompatible with Step 4.  The common positive label is cyclic,
so an exact equivariant transformation has no orthogonal label sector on
which the inverse fold can remain.

The direct estimate leaves a rate parameter for arbitrary approximate
systems. At a finite coefficient quotient the positive and Laurent
elementary images coincide, so the root elements in `(FCM35)` exist. Their
positive word lengths may diverge because the positive presentation realizes
(x_1^{-1}) only through a long finite-quotient collision. Without further
rigidity, retaining the fold would require

\[
\lambda_n^-\eta_n
\tag{FCM37}
\]

bounded away from zero along the marked sector.

For exact representations of the fixed Kazhdan base, however, property
`(T)` projects the proposed mixer to an exact base intertwiner at cost
`eta_n/kappa` before the long word is traversed. Exact tangent covariance
then gives `(FCM8a)`, so `(FCM37)` cannot rescue the model. What remains open
is narrower: the base maps or their tangent covariance must themselves be
genuinely nonliftable normalized-Hilbert--Schmidt almost-representations.
