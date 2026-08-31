---
rg: 2
id: expander-equality-poincare-rounding-proof
kind: route
title: Poincare rounding for the occurrence-four expander equality compiler
target: expander-equality-splitting-is-a-robust-occurrence-four-compiler
requires:
  - cyclic-occurrence-splitting-makes-every-lcs-cubic
---

# Poincare rounding for the occurrence-four expander equality compiler

## 1. A cubic family at every required scale

Marcus, Spielman, and Srivastava prove that every finite regular bipartite
Ramanujan graph has a 2-lift which is again Ramanujan; iterating from
\(K_{3,3}\) gives connected 3-regular bipartite Ramanujan graphs on

$$
n_k=6\cdot 2^k
\qquad(k\geq0)
$$

vertices.  See [Interlacing families I, Annals of Mathematics 182 (2015),
especially the 2-lift construction and main
theorem](https://doi.org/10.4007/annals.2015.182.1.7), with the
[open preprint](https://arxiv.org/abs/1304.4132).

All nontrivial adjacency eigenvalues have absolute value at most
\(2\sqrt2\).  Therefore the first positive eigenvalue of the normalized
Laplacian is at least

$$
\lambda_*:=1-\frac{2\sqrt2}{3}>0.                       \tag{1}
$$

The negative trivial eigenvalue of a bipartite graph is irrelevant for this
Poincare gap.  The good new eigenvalues are strictly below \(3\), so the
iterated lifts stay connected.

For an integer \(d\geq3\), choose the least \(n_k\geq d\) and one graph
\(H_d\) at that scale.  Then

$$
d\leq |V(H_d)|\leq2d.                                  \tag{2}
$$

This choice is effective: at each 2-lift one may enumerate the finitely many
edge signings and retain a signing satisfying the guaranteed spectral
bound.  It need not be efficient for the theorem below.  Since a cubic
graph on \(n\) vertices has \(3n/2\) edges, the total number of added
variables and equations is linear in the number of source occurrences.

## 2. The compiler and the exact presentation

Let \(L\) be a binary LCS.  A variable \(x\) appearing \(d_x\geq3\) times is
replaced by generators

$$
(X_{x,u})_{u\in V(H_{d_x})}.
$$

Assign the \(d_x\) old occurrences injectively to vertices of \(H_{d_x}\);
the remaining vertices are padding.  For every edge \(uv\), add the even
equation

$$
X_{x,u}X_{x,v}=1.                                      \tag{3}
$$

Variables of occurrence at most two are left unchanged.

A used copied variable lies in one old context and in three equations (3),
so its total occurrence is four.  A padding variable lies only in its three
edge equations.  Thus the maximum occurrence is four.

In the solution group, (3) and involutivity give

$$
X_{x,u}=X_{x,v}.
$$

Because \(H_{d_x}\) is connected, all copies and all padding generators for
\(x\) are equal.  The extra context commutator on an edge becomes
redundant.  Eliminating all but one copy by Tietze transformations recovers
the original presentation: every old equation and every old context
commutator becomes the corresponding source relator.  Conversely, sending
every copy to \(x\) respects every compiled relator.  These maps are inverse
and fix \(J\), so

$$
\Gamma_{\operatorname{Comp}(L)}\cong\Gamma_L.           \tag{4}
$$

In particular, assigning the same honest source reflection to every copy
gives perfect completeness in finite-dimensional, tracial, or arbitrary
operator representations.

## 3. Hilbert-valued Poincare synchronization

Let \((\mathcal M,\tau)\) be a finite tracial von Neumann algebra and use
the normalized Hilbert--Schmidt norm

$$
\|A\|_2^2=\tau(A^*A).
$$

The proof is dimension-free because \(L^2(\mathcal M,\tau)\) is a Hilbert
space and the scalar graph Poincare inequality holds coordinatewise for
Hilbert-valued functions.

Fix one split variable, abbreviate \(H=H_d\), write \(n=|V(H)|\), and
assign an exact reflection \(X_u\) to every vertex.  Set

$$
\overline X=\frac1n\sum_{u\in V(H)}X_u,
\qquad
V_X=\frac1n\sum_u\|X_u-\overline X\|_2^2.
$$

For a 3-regular graph with normalized-Laplacian gap at least \(\lambda_*\),
Poincare gives

$$
V_X
 \leq \frac1{3\lambda_* n}
       \sum_{uv\in E(H)}\|X_u-X_v\|_2^2.                \tag{5}
$$

Because \(X_u\) is unitary,

$$
\|X_uX_v-I\|_2=\|X_v-X_u\|_2.                           \tag{6}
$$

Define the edge RMS defect

$$
\delta_x^2
 :=\frac1{|E(H)|}\sum_{uv\in E(H)}
       \|X_uX_v-I\|_2^2.
$$

Since \(|E(H)|=3n/2\), (5) and (6) imply

$$
V_X\leq\frac{\delta_x^2}{2\lambda_*}.                   \tag{7}
$$

Let \(U\subseteq V(H)\) be the \(d\) vertices used by source occurrences.
The Hilbert-space pair-variance identity is

$$
\frac1{n^2}\sum_{r,u\in V(H)}\|X_u-X_r\|_2^2=2V_X.
                                                                    \tag{8}
$$

Average over a uniformly random root \(r\), discard from the inner sum all
vertices outside \(U\), and use \(n/d\leq2\):

$$
\begin{aligned}
\mathbb E_r\frac1d\sum_{u\in U}\|X_u-X_r\|_2^2
&\leq\frac1{nd}\sum_{r,u\in V(H)}\|X_u-X_r\|_2^2\\
&=\frac{2n}{d}V_X\\
&\leq\frac{2}{\lambda_*}\delta_x^2.                    \tag{9}
\end{aligned}
$$

Consequently some vertex \(r_x\), possibly a padding vertex, obeys (9).
Choose

$$
\widehat X_x:=X_{r_x}.                                  \tag{10}
$$

This choice is the useful point: the decoder outputs an existing exact
reflection, so no polar decomposition and no additional rounding error are
needed.

Let \(N=\sum_xd_x\) be the total source occurrence count, put the
representative of an unsplit variable equal to that variable, and define

$$
\varepsilon_{\rm eq}^2
 :=\frac1N\sum_{x:d_x\geq3}d_x\delta_x^2.
$$

Multiplying (9) by \(d_x\), summing over \(x\), and dividing by \(N\) gives

$$
R^2:=
\frac1N\sum_{\text{source occurrences }(x,u)}
 \|X_{x,u}-\widehat X_x\|_2^2
\leq\frac{2}{\lambda_*}\varepsilon_{\rm eq}^2.          \tag{11}
$$

No matrix dimension occurs in (11).

## 4. Transfer of every source LCS relator

Fix an order in each source equation.  Let there be \(m\) source equations
\(C\), each of width \(k_C\leq w\), and write \(A_p\) for the copied
reflection at source occurrence \(p\).  Define the equation-normalized
source-relator defect of the copied assignment by

$$
D_{\rm copy}^2
 :=\frac1m\sum_C\left(
 \left\|\prod_{p\in C}A_p-J^{b_C}\right\|_2^2
 +\sum_{\{p,q\}\subseteq C}
   \|A_pA_qA_pA_q-I\|_2^2
 \right).                                               \tag{12}
$$

Thus (12) includes the product relator and every context commutator.  Let
\(D_{\rm dec}\) be the same expression with \(A_p\) replaced by the
representative \(\widehat A_p\), and abbreviate

$$
r_p:=\|A_p-\widehat A_p\|_2.
$$

Telescoping products of unitaries gives, for every context,

$$
\left\|\prod_{p\in C}\widehat A_p-\prod_{p\in C}A_p\right\|_2
 \leq\sum_{p\in C}r_p.                                  \tag{13}
$$

The same four-factor telescoping gives, for a pair,

$$
\|\widehat A_p\widehat A_q\widehat A_p\widehat A_q
      -A_pA_qA_pA_q\|_2
 \leq2(r_p+r_q).                                        \tag{14}
$$

The squared product changes satisfy

$$
\sum_C\left(\sum_{p\in C}r_p\right)^2
 \leq w\sum_pr_p^2.                                     \tag{15}
$$

For the commutators,

$$
\begin{aligned}
\sum_C\sum_{\{p,q\}\subseteq C}4(r_p+r_q)^2
&\leq8\sum_C(k_C-1)\sum_{p\in C}r_p^2\\
&\leq8w\sum_pr_p^2.                                     \tag{16}
\end{aligned}
$$

Regard all defects in (12) as one Hilbert direct-sum vector.  Equations
(13)--(16), Minkowski's inequality, and
\(N/m=(1/m)\sum_Ck_C\leq w\) yield

$$
\begin{aligned}
D_{\rm dec}
&\leq D_{\rm copy}
 +\left(\frac{9w}{m}\sum_pr_p^2\right)^{1/2}\\
&\leq D_{\rm copy}+3wR\\
&\leq D_{\rm copy}
 +3w\sqrt{\frac2{\lambda_*}}\,\varepsilon_{\rm eq}.     \tag{17}
\end{aligned}
$$

This is the claimed total soundness bound.  The commutator in an added
two-variable equality context needs no separate hypothesis: if
\(U=X_uX_v\), then

$$
\|X_uX_vX_uX_v-I\|_2=\|U^2-I\|_2
 \leq2\|U-I\|_2.                                       \tag{18}
$$

Hence the equality product defect already controls the complete equality
context.

The normalization of \(\varepsilon_{\rm eq}\) is also compatible with a
linear-size constraint tester.  Indeed,
\(d_x\leq n_x\leq2d_x\) and \(|E(H_x)|=3n_x/2\), so its edge weights differ
only by absolute factors from sampling all added equality edges relative to
the source occurrence count.

## 5. Why occurrence three cannot give this expander decoder

Consider any compiler of the same pairwise-equality form in which every
copy is used in one source equation.  If total occurrence is at most three,
each copy can lie in at most two equality equations.  To identify all
\(d\) copies exactly, the equality graph must be connected.  Ignoring
tautological loops, a connected graph of maximum degree two is a path or a
cycle.

Use the normalized trace on \(M_2(\mathbb C)\) and the Pauli reflections

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

Along the path or cyclic order, set

$$
R_j=\cos(2\pi j/d)Z+\sin(2\pi j/d)X,
\qquad 0\leq j<d.                                      \tag{19}
$$

Since \(XZ=-ZX\), every \(R_j\) is an exact reflection.  Adjacent vertices
have

$$
\|R_jR_{j+1}-I\|_2^2
 =\|R_j-R_{j+1}\|_2^2
 =4\sin^2(\pi/d).                                      \tag{20}
$$

For a cycle, the closing edge has the same value; for a path, (20) holds on
every edge present.  On the other hand, the roots-of-unity identity gives

$$
\frac1d\sum_{j=0}^{d-1}R_j=0.
$$

Therefore, for every reflection \(Q\in M_2(\mathbb C)\),

$$
\frac1d\sum_{j=0}^{d-1}\|R_j-Q\|_2^2
 =\frac1d\sum_j\tau(R_j^2)+\tau(Q^2)
  -2\operatorname{Re}\tau\left(\left(\frac1d\sum_jR_j\right)Q\right)
 =2.                                                    \tag{21}
$$

The ratio of (21) to the edge energy (20) is

$$
\frac{1}{2\sin^2(\pi/d)}=\Theta(d^2).                  \tag{22}
$$

Thus the quadratic Poincare degeneration of paths and cycles is realized
already by exact \(2\times2\) reflections; it is not an artifact of allowing
arbitrary Hilbert-valued vectors.  Any RMS synchronization constant grows
linearly in \(d\).  Cubic equality degree—and therefore occurrence four
when each copy also has one source occurrence—is the first degree at which
this pairwise-equality compiler can have a uniform spectral decoder.

## 6. Scope

Equations (4), (11), and (17) prove an exact, perfect-completeness,
dimension-free robust compiler.  They do not produce a source LCS with a
commuting-versus-finite perfect gap, and they do not address higher-arity
synchronization gadgets under the occurrence-three budget.  Those remain
separate gates.
