# LXI: arbitrary unitary functions in alternating conjugates

Date: 2026-09-05. **Complete proof for one function and for compatible families.**
No unrestricted unitary-group statement or LXI resolution is asserted.

## 1. Setup

Retain the properly infinite full free envelope
\[
B=A_{\mathrm{LIX}}*_{\mathbb C}T_2
\]
and its unitary \(v\), chosen with \(\sigma(v)=S^1\).
The isometric universal subalgebra
\[
C=C^*(v,T_2)\cong C(S^1)*_{\mathbb C}T_2
\]
is justified by Armstrong–Dykema–Exel–Li, Proposition 2.2.
[Primary paper](https://arxiv.org/pdf/math/0210448).

The earlier alternating-word result permitted only integer
powers of \(v\). The following replaces one such generator
by an arbitrary continuous unitary function of \(v\), and
allows that same function to occur any finite number of times.

**Theorem 1.** Fix \(f\in C(S^1,S^1)\). Let \(w\) be any finite
product of unitaries from \(T_2\), integer powers of \(v\), and
integer powers of \(f(v)\). For every nontrivial projection
\(p\in T_2\),
\[
\|[v,wpw^*]\|=1.
\tag{1.1}
\]
An arbitrary additional unitary function \(g(v)\) may multiply
\(w\) on the left without changing this conclusion.

In particular, for arbitrary \(a,b\in U(T_2)\),
\[
w=a f(v)b
\tag{1.2}
\]
cannot produce a strict BRR commutator squeeze. This includes
a genuine arbitrary continuous function, not merely a
Laurent polynomial or a norm estimate near a monomial.

For \(p=s_1s_1^*\), both \(wpw^*\) and its complement are
properly infinite and full.

## 2. An antipodal normalization lemma

**Lemma 2.** If \(f:S^1\to S^1\) is continuous of degree \(k\),
then there is \(z\in S^1\) such that
\[
f(-z)=(-1)^k f(z).
\tag{2.1}
\]

**Proof.** Choose a continuous lift \(F:\mathbb R\to\mathbb R\)
with
\[
f(e^{i\theta})=e^{iF(\theta)},\qquad
F(\theta+2\pi)=F(\theta)+2\pi k.
\]
The continuous real function
\[
d(\theta)=F(\theta+\pi)-F(\theta)-\pi k
\]
satisfies \(d(\theta+\pi)=-d(\theta)\). It therefore vanishes
somewhere by the intermediate value theorem. Exponentiating
at such a point proves (2.1). \(\square\)

The sign in (2.1) is determined by the degree parity. The
lemma does not say that \(f\) is a monomial, nor that it has
any special form away from the chosen antipodal pair.

## 3. The two-site flip representation

Let
\[
D=T_2\otimes_{\min}T_2,\qquad
\alpha(a\otimes b)=b\otimes a.
\]
Use the full crossed product
\[
E=D\rtimes_\alpha(\mathbb Z/2)
\]
and its implementing symmetry \(U=U^*=U^{-1}\), so that
\(UdU=\alpha(d)\).

The two site inclusions in \(D\) are faithful by the spatial
tensor-product norm. The coefficient inclusion \(D\to E\)
is faithful as well. Explicitly, for any faithful
\(\rho:D\to B(\mathcal H)\), the representation
\[
d\longmapsto
\begin{pmatrix}\rho(d)&0\\0&\rho(\alpha(d))\end{pmatrix},
\qquad
U\longmapsto
\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]
is covariant and faithful on \(D\).

Choose \(z\) as in Lemma 2. The full free-product universal
property gives
\[
\Phi:C\to E,\qquad
\Phi(v)=zU,\qquad
\Phi(a)=a\otimes1\quad(a\in T_2).
\tag{3.1}
\]
The functional calculus of the symmetry \(U\) gives
\[
\begin{aligned}
f(zU)
&=f(z)\frac{1+U}{2}+f(-z)\frac{1-U}{2}\\
&=f(z)U^k.
\end{aligned}
\tag{3.2}
\]
Thus each letter \(v^n\) or \(f(v)^m\) in the word becomes
a scalar multiple of a power of the same symmetry \(U\).

Only the universal subalgebra \(C\) is mapped in (3.1).
No extension of \(\Phi\) to all of \(B\) is asserted or used.

## 4. Proof of Theorem 1

Under \(\Phi\), the word \(w\) becomes, up to a scalar,
an alternating product of first-site Toeplitz unitaries
and powers of \(U\). Move each occurrence of \(U\) to the
right using
\[
U(a\otimes1)=(1\otimes a)U.
\]
The result has the form
\[
\Phi(w)=\lambda(c_0\otimes c_1)U^\varepsilon,
\qquad
c_0,c_1\in U(T_2),\quad\varepsilon\in\{0,1\}.
\tag{4.1}
\]
All order within a single site is retained; only distinct
sites are commuted.

If \(\varepsilon=0\), equation (4.1) gives
\[
\Phi(wpw^*)=c_0pc_0^*\otimes1.
\]
If \(\varepsilon=1\), it gives
\[
\Phi(wpw^*)=1\otimes c_1pc_1^*.
\]
In either case the image is a nontrivial projection on
one tensor site, and conjugation by \(\Phi(v)=zU\)
moves the same projection to the other site. Therefore
\[
\|\Phi(vwpw^*v^*-wpw^*)\|=1.
\tag{4.2}
\]
To verify this last equality, write \(P=c_jpc_j^*\).
In a faithful representation of \(T_2\), choose one
nonzero vector in the range of \(P\) and one in its
kernel. Their tensor product witnesses norm \(1\)
for \(P\otimes1-1\otimes P\). The upper bound is \(1\),
and the coefficient inclusion preserves the norm.

By the isometric inclusion \(C\subset B\), (4.2) is a
lower bound for \(\|[v,wpw^*]\|\) in \(B\). The opposite
bound \(1\) holds for every commutator of a unitary
with a projection. This proves (1.1).

If \(g(v)\) multiplies \(w\) on the left, it commutes
with \(v\), so conjugating the commutator by \(g(v)\)
leaves its norm unchanged. Finally, \(s_1s_1^*\) is
equivalent to the properly infinite unit, and its
complement contains \(s_2s_2^*\), also equivalent to
the unit. Unitary conjugation preserves proper
infiniteness and fullness. \(\square\)

## 5. Compatible families of functions

The proof gives the following precise extension.

**Corollary 3.** Let \(\mathcal F\) be any collection of
continuous unitary functions on \(S^1\). Suppose there
is a single \(z\in S^1\) such that
\[
f(-z)/f(z)\in\{1,-1\}\qquad(f\in\mathcal F).
\tag{5.1}
\]
Then (1.1) holds for every finite word whose letters
are Toeplitz unitaries, integer powers of \(v\), and
functions \(f(v)\) with \(f\in\mathcal F\), together
with their inverses.

**Proof.** At the common antipodal pair, every
\(f(zU)\) is a scalar multiple of either \(1\) or
\(U\). The argument of Section 4 applies without
change. \(\square\)

A single \(f\) and all its integer powers satisfy
(5.1), by Lemma 2. So do their products with scalar
multiples of integer powers of the coordinate
function.

Compatibility cannot be presumed for two arbitrary
functions. For example, for \(0<\eta<\pi/4\), put
\[
f_1(e^{i\theta})=\exp(i\eta\cos\theta),\qquad
f_2(e^{i\theta})=\exp(i\eta\sin\theta).
\tag{5.2}
\]
Each has degree zero. The first ratio in (5.1) lies
in \(\{1,-1\}\) only when \(\cos\theta=0\), and the
second only when \(\sin\theta=0\). These cannot hold
simultaneously. The restriction on \(\eta\) ensures
that the ratios cannot equal \(-1\), and can equal
\(1\) only at the indicated zeros.

This shows the boundary of the present proof, not a
strict commutator construction. Words such as
\[
a f_1(v)b f_2(v)c
\]
with independent functions lacking a common pair
remain uncomputed. Arbitrary unitaries formed from
linear combinations and functional calculus, and
words using other generators of \(A\), also remain
outside the theorem.
