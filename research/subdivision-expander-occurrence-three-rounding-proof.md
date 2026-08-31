---
rg: 2
id: subdivision-expander-occurrence-three-rounding-proof
kind: route
title: Subdivision-expander Poincare rounding at occurrence three
target: dummy-subdivided-expanders-give-robust-occurrence-three
requires:
  - expander-equality-splitting-is-a-robust-occurrence-four-compiler
---

# Subdivision-expander Poincare rounding at occurrence three

## 1. Put occurrences on subdivided edges, not cubic vertices

Fix a source variable \(x\) with \(d=d_x\geq3\) occurrences.  Starting from
\(K_{3,3}\), iterated good 2-lifts of Marcus--Spielman--Srivastava give
connected 3-regular bipartite Ramanujan graphs on \(6\cdot2^k\) vertices;
see [Interlacing families I, Annals of Mathematics 182
(2015)](https://doi.org/10.4007/annals.2015.182.1.7) and the
[open preprint](https://arxiv.org/abs/1304.4132).

Choose the least such scale

$$
h=6\cdot2^k\geq d.
$$

Then \(d\leq h\leq2d\).  Let \(H_d\) be one graph at this scale.  It has
\(3h/2\geq d\) edges, so choose \(d\) distinct edges.  Subdivide every chosen
edge once and call the new degree-two vertices

$$
s_1,\ldots,s_d.
$$

Call the subdivided graph \(G_d\).  It is connected and has

$$
n:=|V(G_d)|=h+d\leq3d,
\qquad
m:=|E(G_d)|=\frac{3h}{2}+d,
\qquad
\frac mn\leq\frac43.                                   \tag{1}
$$

The last inequality uses \(h/d\leq2\).

Assign the \(i\)th source occurrence of \(x\) to \(s_i\).  Every old vertex
of \(H_d\) is a dummy variable.  Add the even equality equation

$$
X_uX_v=1                                                \tag{2}
$$

for every \(uv\in E(G_d)\).  A used vertex \(s_i\) occurs in its source
equation and its two incident equality equations, hence three times.  A
dummy core vertex retains degree three and occurs only in equality
equations.  Variables of source occurrence at most two are left unchanged.

The number of variables introduced for \(x\) is \(h+d\leq3d\), and the
number of equality equations is \(3h/2+d\leq4d\).  The construction is
effective: one may enumerate the finitely many signings at each 2-lift and
retain one with the guaranteed Ramanujan spectrum.

## 2. Exact Tietze elimination and perfect completeness

In a binary LCS solution group, (2) between involutory generators implies

$$
X_u=X_v.
$$

Because \(G_d\) is connected, all terminal and dummy generators belonging
to \(x\) are equal.  The edge-context commutators are then redundant.
Eliminate every generator but one.  Repeating independently for every split
source variable turns every copied source equation and source-context
commutator into its original relator.

Conversely, send every terminal and dummy copy for \(x\) to the original
generator \(x\).  This respects all equality and copied source relators.
The two maps are inverse and fix the central involution \(J\).  Therefore

$$
\Gamma_{\operatorname{SubComp}(L)}\cong\Gamma_L.        \tag{3}
$$

The same-copy assignment also proves perfect completeness in every operator
model.

## 3. A Poincare bound after partial edge subdivision

Let \(\mathcal K\) be any Hilbert space and let \(F:V(G_d)\to\mathcal K\).
Write \(a_v\) for its values on the \(h\) core vertices of \(H_d\), \(y_e\)
for the value at the subdivision vertex on a selected edge \(e\), and

$$
\overline a:=\frac1h\sum_{v\in V(H_d)}a_v.
$$

Put

$$
E_G:=\sum_{uv\in E(G_d)}\|F(u)-F(v)\|^2.
$$

The Ramanujan adjacency bound gives the normalized-Laplacian gap

$$
\lambda_*:=1-\frac{2\sqrt2}{3}>0.                       \tag{4}
$$

Thus, on the cubic core,

$$
A:=\sum_{v\in V(H_d)}\|a_v-\overline a\|^2
 \leq\frac1{3\lambda_*}
       \sum_{uv\in E(H_d)}\|a_u-a_v\|^2.                \tag{5}
$$

An unsubdivided edge contributes the same energy to \(H_d\) and \(G_d\).
For a subdivided edge \(e=uv\),

$$
\|a_u-a_v\|^2
 \leq2\bigl(\|a_u-y_e\|^2+\|y_e-a_v\|^2\bigr).
$$

Consequently,

$$
A\leq\frac{2}{3\lambda_*}E_G.                           \tag{6}
$$

For each selected edge \(e\), choose one of its endpoints \(o(e)\).  Every
core vertex is chosen at most three times, because its core degree is three.
Therefore

$$
\begin{aligned}
\sum_{e\ {\rm selected}}\|y_e-\overline a\|^2
&\leq2\sum_e\|y_e-a_{o(e)}\|^2
   +2\sum_e\|a_{o(e)}-\overline a\|^2\\
&\leq2E_G+6A.                                          \tag{7}
\end{aligned}
$$

Adding the core vertices and using (6) gives

$$
\sum_{z\in V(G_d)}\|F(z)-\overline a\|^2
 \leq\left(2+\frac{14}{3\lambda_*}\right)E_G.           \tag{8}
$$

The full vertex mean minimizes squared distance, so (8) is also valid with
\(\overline a\) replaced on the left by the full mean
\(\overline F\).  Define

$$
C_*:=2+\frac{14}{3\lambda_*}.                           \tag{9}
$$

Equation (8) is a uniform Hilbert-valued Poincare inequality for every
partially subdivided graph used by the compiler.

## 4. Select one exact reflection as representative

Now take \(\mathcal K=L^2(\mathcal M,\tau)\) for a finite tracial von
Neumann algebra and suppose every \(X_z:=F(z)\) is an exact reflection.
Define the equality-edge defect

$$
\delta_x^2
 :=\frac1m\sum_{uv\in E(G_d)}\|X_uX_v-I\|_2^2.
$$

Unitary invariance gives

$$
\|X_uX_v-I\|_2=\|X_v-X_u\|_2,
$$

so \(E_G=m\delta_x^2\).  If

$$
V_X:=\frac1n\sum_z\|X_z-\overline X\|_2^2,
$$

then (1), (8), and (9) imply

$$
V_X\leq\frac43C_*\delta_x^2.                            \tag{10}
$$

Let \(U=\{s_1,\ldots,s_d\}\) be the used terminals.  The Hilbert pair-variance
identity and \(n/d\leq3\) give

$$
\begin{aligned}
\mathbb E_{r\in V(G_d)}
 \frac1d\sum_{u\in U}\|X_u-X_r\|_2^2
&\leq\frac1{nd}\sum_{r,z\in V(G_d)}\|X_z-X_r\|_2^2\\
&=\frac{2n}{d}V_X\\
&\leq8C_*\delta_x^2.                                   \tag{11}
\end{aligned}
$$

Choose a vertex \(r_x\) attaining (11), and set

$$
\widehat X_x:=X_{r_x}.
$$

It is an existing exact reflection, even when \(r_x\) is a dummy core
vertex.  With

$$
K_*:=8C_*=16+\frac{112}{3\lambda_*},                   \tag{12}
$$

equation (11) reads

$$
\frac1d\sum_{i=1}^d\|X_{s_i}-\widehat X_x\|_2^2
 \leq K_*\delta_x^2.                                   \tag{13}
$$

Let \(N=\sum_xd_x\) be the total source occurrence count, use an unchanged
variable as its own representative, and define

$$
\varepsilon_{\rm eq}^2
 :=\frac1N\sum_{x:d_x\geq3}d_x\delta_x^2.
$$

Summing (13) yields

$$
R^2:=
\frac1N\sum_{\text{source occurrences }(x,u)}
 \|X_{x,u}-\widehat X_x\|_2^2
 \leq K_*\varepsilon_{\rm eq}^2.                        \tag{14}
$$

This estimate is independent of matrix dimension and all \(d_x\).

## 5. Transfer the whole source presentation

Let the source have \(m_0\) equations \(C\), of widths \(k_C\leq w\).
For copied source-occurrence reflections \(A_p\), define

$$
D_{\rm copy}^2
 :=\frac1{m_0}\sum_C\left(
 \left\|\prod_{p\in C}A_p-J^{b_C}\right\|_2^2
 +\sum_{\{p,q\}\subseteq C}
   \|A_pA_qA_pA_q-I\|_2^2
 \right),                                               \tag{15}
$$

and define \(D_{\rm dec}\) by replacing \(A_p\) with its representative.
Put \(r_p=\|A_p-\widehat A_p\|_2\).  Four-factor and general product
telescoping give

$$
\left\|\prod_{p\in C}\widehat A_p-\prod_{p\in C}A_p\right\|_2
 \leq\sum_{p\in C}r_p,
\qquad
\|\widehat A_p\widehat A_q\widehat A_p\widehat A_q
     -A_pA_qA_pA_q\|_2
 \leq2(r_p+r_q).                                        \tag{16}
$$

Consequently,

$$
\sum_C\left(\sum_{p\in C}r_p\right)^2
 \leq w\sum_pr_p^2,
$$

and

$$
\sum_C\sum_{\{p,q\}\subseteq C}4(r_p+r_q)^2
 \leq8w\sum_pr_p^2.                                     \tag{17}
$$

Minkowski in the direct sum of all relator defect spaces, together with
\(N/m_0\leq w\), now gives

$$
\begin{aligned}
D_{\rm dec}
&\leq D_{\rm copy}
 +\left(\frac{9w}{m_0}\sum_pr_p^2\right)^{1/2}\\
&\leq D_{\rm copy}+3wR\\
&\leq D_{\rm copy}+3w\sqrt{K_*}\,\varepsilon_{\rm eq}. \tag{18}
\end{aligned}
$$

The equality-context commutator is controlled by its product defect:
for \(U=X_uX_v\),

$$
\|X_uX_vX_uX_v-I\|_2=\|U^2-I\|_2\leq2\|U-I\|_2.        \tag{19}
$$

Thus (18) transfers every source solution-group relator and the equality
layer controls its complete two-variable contexts.

## 6. Correct robust boundary

The degree-two path/cycle lower bound in
`expander-equality-poincare-rounding-proof` remains exact when the equality
vertices are precisely the source-occurrence copies: rotating \(2\times2\)
Pauli reflections give edge energy \(\Theta(d^{-2})\) and constant global
distance.

It does not rule out the construction here.  Dummy vertices have no source
occurrence to spend, so they can carry equality degree three; used
subdivision vertices retain equality degree two.  A linear-density cubic
dummy core supplies the missing expansion while every variable still has
total occurrence three.

Therefore maximum occurrence two is the exact graph-incidence barrier,
whereas maximum occurrence three already suffices for both exact
solution-group expressiveness and a uniform pairwise-equality decoder.
This is a bounded-occurrence compiler, not a construction of the missing
perfect commuting-versus-finite-dimensional source gap.
