---
rg: 2
id: perfect-game-loss-actor-variance-and-regular-orbit-proof
kind: route
title: Perfect-game loss forces actor variance and exits the regular compressor orbit
target: perfect-synchbcs-forces-actor-mass-beyond-regular-orbit
requires:
  - perfect-qc-separation-yields-finite-bcs-with-no-matrix-model
  - actor-fourier-mixing-is-the-naimark-defect-of-the-base-povm
  - kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath
  - property-t-actor-keeps-fd-invisible-center-in-lef-models
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - kt-ab-marked-return-is-the-first-mixed-cylinder
---

# Perfect-game loss forces actor variance and exits the regular compressor orbit

## 1. The identity coefficients give a finite-dimensional POVM strategy

Let \(X\) be the finite question set, let \(\mathcal O_x\) be the answer set
for question \(x\), and put

\[
 k=\max_x|\mathcal O_x|.
\]

Write \(V(a,b\mid x,y)\in\{0,1\}\) for the predicate and \(\mu(x,y)\)
for the normalized question distribution. The fixed source satisfies

\[
 \omega^*(G_{\mathrm{game}})\leq\frac12.                   \tag{1}
\]

Suppose the source projections have an exact image in an algebraic crossed
product with locally matricial base:

\[
 P_{x,a}=\sum_g a_{x,a,g}u_g.
\]

There are finitely many source generators, and every identity coefficient
\(A_{x,a}=a_{x,a,1}\) has finite base support. Hence all \(A_{x,a}\) lie
together in one finite matrix algebra. By the coefficient theorem in
`actor-fourier-mixing-is-the-naimark-defect-of-the-base-povm`,

\[
 A_{x,a}\geq0,\qquad
 \sum_{a\in\mathcal O_x}A_{x,a}=1.                         \tag{2}
\]

Thus \((A_{x,a})_a\) is a finite-dimensional POVM for every question.

These POVMs define a finite-dimensional tensor-product correlation

\[
 p(a,b\mid x,y)=\tau(A_{x,a}A_{y,b}).                      \tag{3}
\]

For a matrix block with normalized trace, use a maximally entangled vector,
the transposed POVM \(A_{x,a}^{\mathsf T}\) on Alice's leg, and
\(A_{y,b}\) on Bob's leg. Then (3) is the standard maximally entangled trace
identity. If the finite base block is a direct sum, use its finite tracial
GNS representation, equivalently a finite direct sum of those strategies.
In either form (3) is a valid finite-dimensional quantum correlation.

Consequently its losing probability

\[
 \mathcal L(A)=
 \sum_{x,y}\mu(x,y)
 \sum_{\substack{a,b\\V(a,b\mid x,y)=0}}
 \tau(A_{x,a}A_{y,b})                                      \tag{4}
\]

satisfies

\[
 \mathcal L(A)\geq1-\omega^*(G_{\mathrm{game}})
 \geq\frac12.                                               \tag{5}
\]

## 2. Every losing probability is paid by actor variance

Index a question-answer pair by \(i=(x,a)\). For a directed losing cell
\(i=(x,a)\), \(j=(y,b)\), put

\[
 w_{ij}=\mu(x,y).
\]

The perfect source relation gives \(P_iP_j=0\). Let

\[
 v_i=\tau(A_i-A_i^2)
    =\sum_{g\ne1}\|a_{i,g}\|_2^2.                          \tag{6}
\]

The orthogonality part of the Fourier Gram theorem gives

\[
 \tau(A_iA_j)\leq\sqrt{v_iv_j}
 \leq\frac{v_i+v_j}{2}.                                    \tag{7}
\]

Define the total directed losing incidence at \(i\) by

\[
 d_i=\sum_j(w_{ij}+w_{ji}).                                \tag{8}
\]

For \(i=(x,a)\),

\[
 \sum_jw_{ij}
 \leq k\sum_y\mu(x,y)\leq k,
 \qquad
 \sum_jw_{ji}
 \leq k\sum_y\mu(y,x)\leq k.                               \tag{9}
\]

Thus \(d_i\leq2k\). Summing (7) with the losing-cell weights yields

\[
\begin{aligned}
 \mathcal L(A)
 &\leq\frac12\sum_i d_i v_i\\
 &\leq k\sum_i v_i.
\end{aligned}                                               \tag{10}
\]

Combine (5) and (10):

\[
 \sum_{x,a}v_{x,a}
 \geq\frac{1-\omega^*(G_{\mathrm{game}})}{k}
 \geq\frac1{2k}.                                           \tag{11}
\]

This is (PAM4). If there are \(N\) question-answer generators, at least one
of them satisfies

\[
 \sum_{g\ne1}\|a_{x,a,g}\|_2^2
 \geq\frac1{2kN}.                                          \tag{12}
\]

The conclusion is insensitive to the number of actor Fourier terms and to
the size of the finite spin block.

## 3. The local root-port constant becomes a vertex-cover bound

Let \(Q_i\) be reference base projections. Form an undirected graph
\(\mathcal L_{1/4}\) from any losing cells for which

\[
 \tau(Q_iQ_j)=\frac14.                                     \tag{13}
\]

Set \(\varepsilon_i=\|A_i-Q_i\|_2\). The quarter-overlap theorem says that
every edge satisfies

\[
 \frac14-\varepsilon_i-\varepsilon_j
 \leq3\sqrt{\varepsilon_i\varepsilon_j}.                   \tag{14}
\]

If both endpoint errors were less than \(1/20\), put
\(\varepsilon=\max(\varepsilon_i,\varepsilon_j)<1/20\).
Then (14) would imply

\[
 \frac14-2\varepsilon\leq3\varepsilon,
\]

hence \(\varepsilon\geq1/20\), a contradiction. Therefore

\[
 S=\{i:\varepsilon_i\geq1/20\}
\]

meets every edge and is a vertex cover. If \(M\) is a matching, its edges
have disjoint endpoints, so choosing one endpoint in \(S\) from each edge
gives

\[
 \sum_i\varepsilon_i\geq\frac{|M|}{20}.                    \tag{15}
\]

This is the exact all-context form of the local constant. It applies to any
proposed root-port atlas on the subset of losing cells with the marked
quarter overlap.

## 4. Both positive compressors still give a hyperlinear subcorner

In the pinned \(d=3\) Kun--Thom pair, let

\[
 H=\langle A,B\rangle=SL_3(\mathbf Z).
\]

The orbit \(O=H\Gamma\) of the base coset is a regular \(H\)-set: the map

\[
 H\longrightarrow O,\qquad h\longmapsto h\Gamma            \tag{16}
\]

is equivariant and bijective. This is the established calculation in
`kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath`.

Put

\[
 \Pi_O=E(O)\rtimes H.
\]

After transporting sites through (16), this is exactly the shared-center
regular-action group

\[
 E(SL_3(\mathbf Z))\rtimes SL_3(\mathbf Z)
\]

of
`property-t-actor-keeps-fd-invisible-center-in-lef-models`.
That theorem constructs marked finite models on residual finite quotients,
so \(\Pi_O\) is LEF and in particular hyperlinear. Its common central
involution \(J\) remains nontrivial, and

\[
 p_-=\frac{1-J}{2}\ne0.
\]

Assume there were a unital star homomorphism

\[
 \Phi:\mathcal A_I\longrightarrow p_-\mathbf C[\Pi_O]p_-.
 \tag{17}
\]

The normalized canonical trace on the corner would pull back through
\(\Phi\) to a tracial state on \(\mathcal A_I\). Hyperlinearity of
\(\Pi_O\) makes that corner trace Connes embeddable, and Connes
embeddability passes to the tracial algebra generated by the image.
Therefore the pullback trace would be CE. This contradicts the established
fact that every trace on \(\mathcal A_I\) is non-CE. Hence (17) is
impossible.

This conclusion allows arbitrary finite actor Fourier sums in both \(A\)
and \(B\), all joint \(H\)-multiplication, and every finite spin cylinder on
the regular orbit. It is stronger than saying that one local cell has a
finite absorber: the whole A,B-only algebraic subcorner is excluded.

## 5. Exact surviving interface

Any full Kun--Thom corner map must leave the subcorner of Section 4. Thus at
least one source image must use a base site outside \(O\), an actor
coefficient outside \(H\), or both. Since the full actor is generated by
\(\Gamma,A,B\), this is a genuinely mixed stabilizer/compressor occurrence,
not a larger A,B cylinder.

The first explicit mixed return already recorded in the repository is

\[
 r=e_{12}(x_1)\in\Gamma,\qquad
 h=LrL^{-1}=e_{12}((x_1x_2x_3)^{-1}),                     \tag{18}
\]

where \(L\in H=\langle A,B\rangle\). It moves the base coset to the marked
site \(h\Gamma\), outside the regular orbit. The finite Kazhdan generating
packet of \(\Gamma\) is needed as well: one visible root has exact finite
countermodels.

Equations (11)--(12) show that a hypothetical source atlas brings
macroscopic actor Fourier mass to this mixed interface. Equations
(14)--(15) show that it cannot keep all quarter-overlap root ports sharp.
Section 4 shows that the mass cannot retreat into the complete two-compressor
regular orbit.

No contradiction is proved after the mixed return and Kazhdan rows are
included. The remaining construction/obstruction is to solve the
matrix-valued Fourier Gram equations jointly with (18) and that full packet.
