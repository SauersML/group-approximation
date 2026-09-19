# LXI: a projective-space obstruction for arbitrary mixed unitaries with finite-representation coefficients

Date: 2026-09-05. **Complete proof of the stated norm obstruction.**
This handles arbitrary continuous functional letters and arbitrary unitaries
in the specified subalgebra. It does not settle LXI.

The proof in Sections 3–4 also gives the universal statement directly:
for any unital D with a representation as in (1.1), the circle
generator z of C(S1)*D satisfies ||[z,WpW*]||=1 for every unitary W.
The LIX algebra is needed only for the application, not for this
universal norm theorem. The root reviewer checked the projective-space
argument, both complementary Chern obstructions, the rank-one norm
formula, and the two-projection representation proof; no gap was found.

## 1. Statement

Let \(A\) and \(v\) be the LIX algebra and witness, chosen so that
\(\sigma(v)=S^1\), and put
\[
B=A*_{\mathbb C}T_2.
\]
Let \(D\subset T_2\) be a unital \(C^*\)-subalgebra containing a
projection \(p\). Suppose there is a unital finite-dimensional
representation
\[
\rho:D\to M_N(\mathbb C),
\qquad
0<r:=\operatorname{rank}\rho(p)<N.
\tag{1.1}
\]

**Theorem 1.** For every unitary \(W\in U(C^*(v,D))\),
\[
\boxed{\ \|[v,WpW^*]\|=1.\ }
\tag{1.2}
\]
There is no restriction on the expression for \(W\): it may
involve arbitrary continuous unitary functions of \(v\), linear
combinations of mixed words, and functional calculus.

For \(p=s_1s_1^*\), the projections \(WpW^*\) and
\(1-WpW^*\) are properly infinite and full in \(B\).
Nevertheless, none gives the strict commutator bound in
BRR Lemma 2.4(ii).

The representation (1.1) is a condition on \(D\), not on
\(T_2\) or \(B\). Proper infiniteness does not pass to an
arbitrary unital subalgebra: the isometries witnessing it
need not belong to that subalgebra. Likewise, fullness in
\(T_2\) need not imply fullness in \(D\).
Thus there is no conflict between (1.1) and proper
infiniteness of the ambient Toeplitz factor.

## 2. The universal subalgebra

The common-amalgamating-algebra inclusion theorem gives
isometric embeddings
\[
C(S^1)*_{\mathbb C}D
\longrightarrow
C(S^1)*_{\mathbb C}T_2
\longrightarrow
A*_{\mathbb C}T_2.
\tag{2.1}
\]
Since \(\sigma(v)=S^1\), the first algebra is exactly
\(C^*(v,D)\) under these maps. The source is
Armstrong–Dykema–Exel–Li, *On embeddings of full amalgamated
free product C*-algebras*, Proposition 2.2.
[Primary paper](https://arxiv.org/pdf/math/0210448).

In particular, a representation of
\(C(S^1)*D\) may be used to bound the norm in \(B\).
It need not extend to a representation of all of \(B\).

## 3. A finite-dimensional projective-space test

Let \(X=\mathbb{CP}^{N-1}\), and let
\[
e:X\to M_N(\mathbb C)
\]
be the tautological rank-one projection. Define a continuous
unitary
\[
V(x)=i(2e(x)-1_N).
\tag{3.1}
\]
The universal property provides a unital homomorphism
\[
\Psi:C(S^1)*D\to C(X,M_N),
\qquad
\Psi(v)=V,\quad \Psi(d)(x)=\rho(d).
\tag{3.2}
\]
Write
\[
P=\rho(p),\quad
\mathcal W=\Psi(W),\quad
Q(x)=\mathcal W(x)P\mathcal W(x)^*.
\tag{3.3}
\]
The range bundle of \(Q\) is globally trivial of rank \(r\):
a basis of \(P\mathbb C^N\), transported by \(\mathcal W(x)\),
is a global orthonormal frame. The same argument trivializes
the complementary bundle \(1-Q\), of rank \(N-r\).

Set
\[
\lambda(x)=\operatorname{Tr}(e(x)Q(x))\in[0,1].
\tag{3.4}
\]
Since \(e(x)\) has rank one, \(eQe=\lambda e\).
In the decomposition given by \(e\), the off-diagonal
block of \(Q\) has squared norm \(\lambda-\lambda^2\).
Consequently,
\[
\|[V(x),Q(x)]\|
=2\sqrt{\lambda(x)(1-\lambda(x))}.
\tag{3.5}
\]

We now show that \(\lambda\) must attain both \(0\) and \(1\).

Suppose first that \(\lambda(x)>0\) for every \(x\).
Then \(Q\) restricted to the tautological line bundle \(L\)
is a nowhere-zero bundle homomorphism
\[
L\longrightarrow\operatorname{Ran}(Q)\cong\mathbf1^r.
\]
Equivalently, it is a nowhere-zero section of
\((L^*)^{\oplus r}\). But
\[
c_r((L^*)^{\oplus r})=c_1(L^*)^r\ne0
\quad\text{in }H^{2r}(\mathbb{CP}^{N-1};\mathbb Z),
\tag{3.6}
\]
because \(1\le r\le N-1\). A nowhere-zero section of a
rank-\(r\) complex vector bundle gives a trivial line
summand and forces its top Chern class to vanish,
contradicting (3.6). Therefore \(\lambda=0\) somewhere.

Applying the same argument to \(1-Q\), whose rank is
\(N-r\in\{1,\ldots,N-1\}\), shows that \(1-\lambda=0\)
somewhere. Hence \(\lambda=1\) somewhere. Connectedness
of \(X\) and continuity of \(\lambda\) imply that
\(\lambda=1/2\) at some point \(x_0\). Equation (3.5)
then gives
\[
\|[V(x_0),Q(x_0)]\|=1.
\tag{3.7}
\]

The elementary vector-bundle facts used here are the
projective-space cohomology ring and the top-Chern
obstruction to a nowhere-zero section; see Hatcher,
*Vector Bundles and K-Theory*, §3.1 and Proposition 3.13.
[Author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).

## 4. Proof of Theorem 1

By the isometry (2.1), the representation (3.2), and (3.7),
\[
\|[v,WpW^*]\|_B
\ge\|[\Psi(v),\Psi(WpW^*)]\|
\ge1.
\]
The reverse inequality holds for every unitary and
projection: their commutator is off-diagonal in the
projection decomposition, with both blocks contractions.
This proves (1.2).

For \(p=s_1s_1^*\), one has \(p\sim1\), and \(1-p\)
contains \(s_2s_2^*\sim1\). Both are therefore properly
infinite and full in \(B\). Unitary conjugation preserves
these properties. \(\square\)

## 5. Consequences for two independent functions

The functions
\[
f(e^{i\theta})=\exp(i\eta\cos\theta),\qquad
g(e^{i\theta})=\exp(i\eta\sin\theta),
\qquad 0<\eta<\pi/4,
\tag{5.1}
\]
have no common compatible antipodal pair for the
earlier two-site flip argument.

Theorem 1 nevertheless covers every unitary expression
using both functions, provided all its Toeplitz
coefficients and \(p\) lie in a subalgebra \(D\)
satisfying (1.1). In particular, for any \(a,b,c\in U(D)\),
\[
W=a f(v)b g(v)c
\quad\Longrightarrow\quad
\|[v,WpW^*]\|=1.
\tag{5.2}
\]
Neither the size of \(\eta\) nor the particular formulas
in (5.1) are needed for this conclusion: arbitrary
continuous unitary functions are allowed.

A useful sufficient condition is that \(D\) be residually
finite-dimensional and \(0<p<1\). Choose finite-dimensional
representations nonzero on \(p\) and on \(1-p\), and take
their direct sum. It satisfies (1.1). In particular,
every finite-dimensional \(D\) containing \(p\) qualifies.

## 6. A concrete two-projection coefficient class

Let \(p,r_0\in T_2\) be any two projections, with \(0<p<1\),
and let
\[
D=C^*(1,p,r_0).
\]
Then \(D\) is residually finite-dimensional. Here is the
short structural verification, so that this corollary
does not rely on an unexplained classification assertion.

The element
\[
c=(p-r_0)^2=p+r_0-pr_0-r_0p
\]
commutes with both generating projections. In an irreducible
representation it is a scalar \(t1\), \(0\le t\le1\).
If \(t=0\), the two represented projections coincide.
If \(t=1\), they are complementary. These cases generate
a commutative algebra and have one-dimensional irreducible
representations.

For \(0<t<1\), decompose by the represented projection \(p\).
The equation \(c=t1\) gives
\[
r_0=
\begin{pmatrix}
(1-t)1&b\\
b^*&t1
\end{pmatrix},
\qquad
bb^*=t(1-t)1,\quad b^*b=t(1-t)1.
\]
Thus \(b/\sqrt{t(1-t)}\) identifies the two summand Hilbert
spaces unitarily. In that identification the generated
algebra is \(M_2(\mathbb C)\otimes1\).
Irreducibility forces the multiplicity to be one.
Every irreducible representation of \(D\) consequently
has dimension at most two. Since irreducible
representations separate points of a \(C^*\)-algebra,
\(D\) is residually finite-dimensional.

It follows that all choices
\[
a,b,c\in U(C^*(1,p,r_0))
\]
in (5.2) give norm exactly \(1\). For example, this
includes arbitrary phase rotations
\[
a=\exp(i\alpha p),\qquad b=\exp(i\beta r_0)
\]
and arbitrary additional unitary coefficients in the
same two-projection algebra. The inserted functions
of \(v\) may be the independent pair (5.1), or any
other pair.

## 7. Boundary of the result

The theorem controls all unitaries in \(C^*(v,D)\),
rather than only alternating products, whenever \(D\)
has a finite-dimensional representation detecting
both sides of \(p\). It does not provide such a
representation for \(D=T_2\): a unital properly infinite
algebra has no nonzero unital finite-dimensional
representation.

Thus an unrestricted Toeplitz-coefficient construction
could still escape by generating a subalgebra with no
finite-dimensional representation satisfying (1.1).
No strict commutator example in that remaining class
has been constructed here. The free-envelope witness's
non-nullness remains unproved, and LXI remains open.
