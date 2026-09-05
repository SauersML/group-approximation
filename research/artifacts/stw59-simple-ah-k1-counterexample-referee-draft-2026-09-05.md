# A simple AH algebra which is not \(K_1\)-injective

**Referee-ready revision.** This note reorganizes the proof of the simple-AH counterexample so that the direct obstruction to \(K_1\)-injectivity is the main theorem, and the stronger computation \(K_1(A)=0\) is clearly separated as an additional conclusion. The underlying mathematics is the same as in `stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`.

## Abstract

We construct a separable, simple, unital, nuclear, stably finite AH algebra \(A\) and a unitary \(v\in U(A)\) such that
\[
v\notin U_0(A),\qquad \operatorname{diag}(v,1_A)\in U_0(M_2(A)).
\]
Hence the canonical map
\[
U(A)/U_0(A)\longrightarrow K_1(A)
\]
is not injective, giving a negative answer to Problem LIX of Schafhauser--Tikuisis--White. In fact \(v^2\in U_0(A)\) and \(K_1(A)=0\).

The mechanism is an unstable order-two class in \(\pi_4(U(2))\), protected against cancellation by a Chern-parity obstruction. An isomorphism of two complementary bundles would produce a mapping-torus bundle with odd top Chern number, whereas integral \(K\)-theory forces every such mapping torus to have even top Chern number. Twisted point-evaluation maps then make the inductive limit simple while preserving the obstruction.

## 1. Main theorem and proof architecture

For a unital \(C^*\)-algebra \(B\), write \(U_0(B)\) for the norm-connected component of \(1\) in \(U(B)\). Recall that \(B\) is \(K_1\)-injective when the canonical map
\[
\kappa_B:U(B)/U_0(B)\longrightarrow K_1(B)
\]
is injective.

**Theorem A.** There exist a separable, simple, unital, nuclear, stably finite, infinite-dimensional AH algebra \(A\) and \(v\in U(A)\) with
\[
v\notin U_0(A),\qquad \operatorname{diag}(v,1_A)\in U_0(M_2(A)).
\]
Consequently \(A\) is not \(K_1\)-injective. Moreover
\[
v^2\in U_0(A),\qquad K_1(A)=0.
\]

The proof has four steps.

1. Choose the nonzero element \(u\in\pi_4(U(2))\cong\mathbb Z/2\). It dies after one stabilization because \(\pi_4(U(3))=0\).
2. Protect \(u\) from becoming null-homotopic at finite stages by twisting the spare directions with tautological line bundles. The protection is the odd-versus-even mapping-torus Chern-number contradiction proved below.
3. Use dense twisted point evaluations to build a simple AH limit while preserving the protected class at every finite stage.
4. Use finite-stage detection of null-homotopy to show the class remains nontrivial in the limit. Its stabilized contraction survives automatically, so \(K_1\)-injectivity fails.

The direct stabilized contraction is logically enough for the negative answer; the computation \(K_1(A)=0\) is an independent strengthening.

## 2. The finite bundle obstruction

Fix positive integers \(d_1,\ldots,d_\ell\), put
\[
Y=\prod_{j=1}^{\ell}\mathbb{CP}^{d_j},\qquad
m=\sum_{j=1}^{\ell}d_j,
\]
and let
\[
H=\bigoplus_{j=1}^{\ell}L_j^{\oplus d_j},
\]
where \(L_j\) is the pullback of the tautological line bundle from the \(j\)-th factor. Write \(h_j=c_1(L_j)\). Then
\[
H^*(Y;\mathbb Z)=
\mathbb Z[h_1,\ldots,h_\ell]/(h_1^{d_1+1},\ldots,h_\ell^{d_\ell+1})
\]
and
\[
c_m(H)=\prod_j h_j^{d_j},\qquad
\left|\langle c_m(H),[Y]\rangle\right|=1.
\tag{2.1}
\]
The empty product is allowed, with \(Y\) a point and \(H=0\).

Regard \(S^5\subset\mathbb C^3\) as the unit sphere and let
\[
F_x=x^\perp\subset\mathbb C^3.
\]
Thus \(F\) is a rank-two bundle with \(F\oplus\mathbf1\cong\mathbf1^3\).

**Proposition 2.1 (twisted cancellation failure).** On \(S^5\times Y\),
\[
F\oplus H\not\cong\mathbf1^2\oplus H.
\tag{2.2}
\]

The proof is an odd-versus-even contradiction.

### 2.1. Every relevant mapping torus has even top Chern number

Set
\[
M=S^5\times Y,\qquad V=\mathbf1^3\oplus H,\qquad r=m+3.
\]

**Lemma 2.2 (mapping-torus parity).** Let \(W\) be a rank-\(r\) complex vector bundle over \(S^1\times M\) whose restriction to one \(M\)-slice is isomorphic to \(V\). Then
\[
\left\langle c_r(W),[S^1\times M]\right\rangle\in2\mathbb Z.
\tag{2.3}
\]

**Proof.** Let \(p:S^1\times M\to M\) be projection and put
\[
\delta=[W]-[p^*V]\in K^0(S^1\times M).
\]
Since \(K^1(Y)=0\) and \(K^0(Y)\) is free abelian, generated additively by line monomials, the Kunneth decomposition of the restriction kernel gives
\[
\operatorname{ch}(\delta)=z\,\operatorname{ch}(\beta)
\tag{2.4}
\]
for some \(\beta\in K^0(Y)\), where \(z=tx\), with \(t\in H^1(S^1;\mathbb Z)\) and \(x\in H^5(S^5;\mathbb Z)\) integral generators. We choose the odd \(K\)-theory generator on \(S^5\) with Chern-character coefficient one, as supplied by suspension of the Bott generator.

Because \(z^2=0\), the logarithm of the total Chern class has no nontrivial products, and hence
\[
c_q(\delta)=(-1)^{q-1}(q-1)!\operatorname{ch}_q(\delta).
\tag{2.5}
\]
Take first a line monomial \(\beta=\prod_jL_j^{a_j}\). For a multi-index \(b\) with \(|b|=q-3\), the coefficient of \(z\prod_jh_j^{b_j}\) is
\[
(-1)^{q-1}(|b|+2)(|b|+1)
\binom{|b|}{b_1,\ldots,b_\ell}
\prod_j a_j^{b_j}.
\tag{2.6}
\]
This is even, since \((|b|+1)(|b|+2)\) is a product of consecutive integers. By linearity the same divisibility holds for every \(\beta\in K^0(Y)\). The integral cohomology of \(S^1\times S^5\times Y\) is torsion-free, so this rational Chern-character computation determines the integral coefficients.

Finally
\[
c(W)=c(p^*V)c(\delta).
\]
Since \(V\) is pulled back from the \(2m\)-dimensional space \(Y\), while \(2r=2m+6\), its top class \(c_r(V)\) vanishes. Every surviving contribution to \(c_r(W)\) contains a positive Chern class of \(\delta\), hence is even. This proves (2.3). \(\square\)

### 2.2. A hypothetical cancellation produces an odd mapping torus

**Proof of Proposition 2.1.** Give \(V=\mathbf1^3\oplus H\) its direct-sum Hermitian metric. There are unit sections
\[
e(x,y)=(e_3,0),\qquad s(x,y)=(x,0),
\]
with
\[
e^\perp=\mathbf1^2\oplus H,\qquad s^\perp=F\oplus H.
\]
If the complements were isomorphic, polar decomposition would give a unitary isomorphism between them. Extend it by \(e\mapsto s\) to obtain a unitary bundle automorphism \(g\) of \(V\) satisfying \(ge=s\).

Form the mapping torus
\[
W_g=(V\times[0,1])/((v,1)\sim(g^{-1}v,0))
\longrightarrow S^1\times M.
\tag{2.7}
\]
Choose a smooth section \(\sigma\) of \(H\), transverse to zero, whose zero number is \(\pm\langle c_m(H),[Y]\rangle=\pm1\), and choose \(\chi:[0,1]\to[0,1]\) that vanishes near the endpoints and equals \(1\) near \(1/2\). Then
\[
S(x,y,t)=((1-t)e_3+tx,\chi(t)\sigma(y))
\tag{2.8}
\]
descends to a section of \(W_g\). Its zeros occur exactly when
\[
t=\tfrac12,\qquad x=-e_3,\qquad \sigma(y)=0.
\]
At \((-e_3,1/2)\), the derivative in the \(S^5\times[0,1]\) variables is
\[
T_{-e_3}S^5\oplus\mathbb R\longrightarrow\mathbb C^3,\qquad
(\xi,a)\longmapsto\tfrac12\xi-2ae_3,
\]
a real-linear isomorphism. Thus the total local index of the zeros of \(S\) is \(\pm1\). Since for a complex bundle the Euler class of the underlying oriented real bundle is its top Chern class,
\[
\left\langle c_r(W_g),[S^1\times M]\right\rangle=\pm1.
\]
This contradicts Lemma 2.2. \(\square\)

The use of an arbitrary automorphism \(g\) is important: the argument excludes every possible isomorphism of the two complements, not merely a particular contraction through a chosen trivial line.

## 3. The unstable unitary

The frame fibration
\[
U(2)\longrightarrow U(3)\longrightarrow S^5,\qquad a\mapsto ae_3,
\]
is associated to \(F\). Bott's unstable computation gives
\[
\pi_4(U(2))\cong\mathbb Z/2,\qquad \pi_4(U(3))=0.
\]
Fix a based representative
\[
u:S^4\longrightarrow U(2)
\]
of the nonzero class. Its clutching bundle is \(F\). Also \(u^2\simeq1\), and \(u\oplus1:S^4\to U(3)\) is null-homotopic.

Put
\[
X=S^4\times Y,\qquad E=\mathbf1^2\oplus H,\qquad
B=\Gamma(X,\operatorname{End}(E)),
\]
and let \(w=u\oplus1_H\in U(B)\).

**Corollary 3.1.** One has
\[
w\notin U_0(B),\qquad w^2\in U_0(B),\qquad
\operatorname{diag}(w,1_E)\in U_0(M_2(B)).
\]

**Proof.** Clutching the two hemispheres of \(S^5\) by \(w\) produces \(F\oplus H\). If \(w\) were null-homotopic, changing one hemisphere trivialization along a contraction would identify this bundle with the identity-clutched bundle \(\mathbf1^2\oplus H\), contradicting Proposition 2.1. The other two claims follow from \(u^2\simeq1\) and \(u\oplus1\simeq1\). \(\square\)

Thus the finite-stage obstruction already has exactly the form needed for failure of \(K_1\)-injectivity: nontrivial before stabilization, trivial after one stabilization.

## 4. The simple twisted AH tower

Set
\[
r_i=2^{i+1},\qquad
Y_i=\prod_{j=0}^{i-1}\mathbb{CP}^{r_j},\qquad
X_i=S^4\times Y_i,
\]
and
\[
H_i=\bigoplus_{j=0}^{i-1}L_{j+1}^{\oplus r_j},
\qquad E_i=\mathbf1^2\oplus H_i,
\qquad A_i=\Gamma(X_i,\operatorname{End}(E_i)).
\tag{4.1}
\]
Then
\[
\operatorname{rank}(E_i)=r_i,\qquad \dim_{\mathbb R}(X_i)=2r_i.
\]

Choose points \(x_i\in X_i\) so that for each fixed \(k\), the tail
\[
\{\pi_{k,i}(x_i):i\ge k\}
\]
is dense in \(X_k\). Using an identification \(E_i(x_i)\cong\mathbb C^{r_i}\), the bundle decomposition
\[
E_{i+1}\cong\pi_i^*E_i\oplus(E_i(x_i)\otimes L_{i+1})
\]
defines an injective unital homomorphism
\[
\varphi_i(a)=\pi_i^*a\oplus(a(x_i)\otimes1_{L_{i+1}}).
\tag{4.2}
\]
Let
\[
A=\varinjlim(A_i,\varphi_i).
\tag{4.3}
\]

The second summand is the essential twist. A scalar point-evaluation block would add globally trivial directions and can destroy the unstable class. Here every new point-evaluation direction is tensored with the new tautological line, and its multiplicity is exactly the complex dimension of the new projective factor. This is precisely the configuration to which Proposition 2.1 reapplies at every stage.

## 5. Structure of the limit

**Lemma 5.1.** The algebra \(A\) is separable, simple, unital, nuclear, stably finite and infinite-dimensional.

**Proof.** Separability, unitality and nuclearity are immediate from the homogeneous building blocks and the countable inductive system. Infinite-dimensionality follows from the injective copy of \(A_0=M_2(C(S^4))\).

For simplicity, let \(0\ne a\in(A_k)_+\). Choose \(i\ge k\) so that \(\pi_{k,i}(x_i)\) lies in the nonempty open set where \(a\) is nonzero. Then the coordinate copy of \(a\) survives to stage \(i\) and is nonzero at \(x_i\). The point-evaluation block in the next connecting map is therefore nonzero in every fiber of \(A_{i+1}\), so the image is full. A standard positive cut-down argument then shows every nonzero ideal in the limit contains a full stage element, hence the unit.

Each \(A_i\) has tracial states. Compactness of the inverse system of trace spaces gives a trace on \(A\); simplicity makes it faithful. Its matrix amplifications are faithful, so no matrix algebra over \(A\) contains an infinite projection. Hence \(A\) is stably finite. \(\square\)

For the additional \(K_1\)-computation, every \(X_i\) has an even-cell CW decomposition, hence \(K^1(X_i)=0\). Since \(A_i\) is Morita equivalent to \(C(X_i)\), \(K_1(A_i)=0\), and continuity gives
\[
K_1(A)=0.
\tag{5.1}
\]
Again, (5.1) is stronger than needed for the negative answer.

## 6. Persistence of the obstruction

Let \(v_i=\varphi_{0,i}(u)\in U(A_i)\), and put
\[
w_i=u\oplus1_{H_i}.
\]

**Lemma 6.1.** For every \(i\), \(v_i\) is homotopic to \(w_i\), and \(w_i\notin U_0(A_i)\).

**Proof.** The assertion is clear at stage zero. If it holds at stage \(i\), then after applying \(\varphi_i\), the extra point-evaluation block is
\[
w_i(x_i)\otimes1_{L_{i+1}}.
\]
Because the matrix \(w_i(x_i)\in U(r_i)\) is connected to \(1\), this entire line-twisted block contracts globally. What remains is precisely \(w_{i+1}\). Proposition 2.1, with \(d_j=r_{j-1}\), shows \(w_i\notin U_0(A_i)\). \(\square\)

We also need the elementary finite-stage detection fact.

**Lemma 6.2.** Let \(B=\overline{\bigcup_iB_i}\) be an increasing union of unital \(C^*\)-algebras. If \(a\in U(B_k)\cap U_0(B)\), then \(a\in U_0(B_j)\) for some \(j\ge k\).

**Proof.** Approximate a norm-continuous path from \(a\) to \(1\) by finitely many sufficiently close elements in one stage. Polar decomposition turns those approximants into nearby unitaries in that stage; any two unitaries at distance less than \(2\) are joined by the principal logarithm. Concatenating gives a stagewise path. \(\square\)

**Proof of Theorem A.** Let \(v\in U(A)\) be the image of \(u\). If \(v\in U_0(A)\), Lemma 6.2 would imply \(v_i\in U_0(A_i)\) for some \(i\), contradicting Lemma 6.1. Thus \(v\notin U_0(A)\).

On the other hand, the fixed null-homotopy of \(\operatorname{diag}(u,1_2)\) maps through the inductive system to a null-homotopy of \(\operatorname{diag}(v,1_A)\) in \(M_2(A)\). Hence the nonzero class of \(v\) in \(U(A)/U_0(A)\) maps to zero after stabilization, so \(\kappa_A\) is not injective. The same argument with \(u^2\) gives \(v^2\in U_0(A)\), and (5.1) gives \(K_1(A)=0\). \(\square\)

## 7. Relation to existing regularity results

The counterexample does not contradict the positive \(K\)-stability results for diagonal AH algebras. In an ordinary diagonal AH system, scalar eigenvalue maps add trivial matrix directions. Here the building blocks are endomorphism bundles and the evaluation multiplicities are line-twisted. That distinction is exactly what lets the unstable class survive.

Elliott--Ho--Toms prove stable rank one for a large class of simple diagonal AH systems, and Seth proves \(K\)-stability for simple infinite-dimensional unital diagonal AH algebras. The present system lies outside those hypotheses. Its dimension-to-rank ratio is
\[
\frac{\dim X_i}{\operatorname{rank}E_i}=2
\]
at every stage, so no small dimension-to-rank mechanism is available.

The construction addresses simplicity without proper infiniteness. It does not answer the separate question whether every properly infinite unital \(C^*\)-algebra is \(K_1\)-injective.

## 8. Verification boundary

The proof is complete at manuscript level and has survived independent internal re-readings. It has not yet been externally peer reviewed, and the full endpoint is not yet formally verified in Lean.

The standard external inputs used here are:

- Bott's calculation \(\pi_4(U(2))\cong\mathbb Z/2\) and \(\pi_4(U(3))=0\);
- the identification of the clutching boundary with the bundle \(F\);
- projective-space complex \(K\)-theory and the torsion-free Kunneth theorem;
- the Chern-character normalization of the sphere Bott generator;
- the equality of the Euler class of a complex bundle with its top Chern class.

The current Lean formalization has already isolated the direct endpoint criterion: a single unitary with
\[
u\notin U_0(A),\qquad \operatorname{diag}(u,1)\in U_0(M_2(A))
\]
refutes \(K_1\)-injectivity, so the formal proof need not compute \(K_1(A)=0\). The remaining hard formalization work is topological: formalizing the parity obstruction and the passage from the explicit isolated zero to the nonzero mod-two Euler/top-Chern class.

## References

[Bott] R. Bott, *The stable homotopy of the classical groups*, Ann. of Math. (2) **70** (1959), 313--337.

[EHT] G. A. Elliott, T. M. Ho, A. S. Toms, *A class of simple \(C^*\)-algebras with stable rank one*, J. Funct. Anal. **256** (2009), 307--322.

[Hatcher] A. Hatcher, *Vector Bundles and K-Theory*, Version 2.2, 2017.

[Schochet] C. Schochet, *Topological methods for \(C^*\)-algebras II: Geometric resolutions and the Kunneth formula*, Pacific J. Math. **98** (1982), 443--458.

[Seth] A. Seth, *Tensorial Permanence of \(K\)-Stability for Diagonal AH-Algebras*, Bull. Lond. Math. Soc. **58** (2026).

[STW] C. Schafhauser, A. Tikuisis, S. White, *Nuclear \(C^*\)-algebras: 99 problems*, arXiv:2506.10902, Problem LIX.

[Villadsen] J. Villadsen, *On the stable rank of simple \(C^*\)-algebras*, J. Amer. Math. Soc. **12** (1999), 1091--1102.
