# Root receivers: an exact centralizer obstruction and a compression calibration

2026-09-08. Handwritten group and matrix arguments; no computation or
build. These results test two proposed ways to recover a common
additive coefficient receiver from Leavitt microstates. They do not
decide hyperlinearity of the full group.

Let \(R=L_{\mathbb F_2}(1,2)\), with
\(t_i s_j=\delta_{ij}\) and \(s_0t_0+s_1t_1=1\). Write
\(s_\alpha=s_{\alpha_1}\cdots s_{\alpha_k}\) and
\(t_\alpha=t_{\alpha_k}\cdots t_{\alpha_1}\).
Use the established identification \(H=\mathrm{GL}_3(R)
=\mathrm{EL}_3(R)\), and put

\[
U=\{x_{12}(r)=I+rE_{12}:r\in R\},\qquad
v=s_0t_1+s_1t_0.
\]

The group \(U\) is the additive \(\mathbb F_2\)-vector space of
\(R\). All Hilbert--Schmidt norms below use normalized trace.

## 1. One constant root does not double-centralizer-define the full root

Let

\[
a=x_{12}(1),\qquad b_1=x_{12}(s_0),\qquad
b_3=x_{12}(v),\qquad K=\operatorname{diag}(v,v,1).
\]

Since \(v^2=1\), direct multiplication gives

\[
[K,a]=1,\qquad [K,b_1]=x_{12}(v s_0v+s_0).       \tag{1}
\]

The second element is nonidentity. In fact \(vs_0=s_1\), so its
coefficient has the explicit sandwich

\[
t_1(vs_0v+s_0)v=1.                               \tag{2}
\]

Thus \(K\in C_H(a)\) but \(b_1\notin C_H(C_H(a))\). The
full coefficient root \(U\) cannot be recovered as the double
centralizer of this constant root, even inside the actual group
\(H\). This is not merely a discrepancy caused by replacing \(H\)
with an ambient unitary group.

The witness is a literal finite word in the frozen generators. With
\(c=(123)\), \(b_2=x_{12}(t_0)\), and
\(\gamma(W)=cWc^{-1}\), use the
[finite coefficient packet](leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md):

\[
d=[b_2,\gamma(b_1)],\quad h=\gamma^2(d),\quad
a=[d,h],\quad e=\gamma(d),\quad j=aea^{-1}.
\]

Their native values are \(d=x_{13}(1)\), \(a=x_{12}(1)\),
\(e=x_{21}(1)\), and \(j=(12)\). On the first two coordinates,
\((x_{12}(v)j)^3=\operatorname{diag}(v,v)\). Consequently

\[
K=(b_3j)^3.                                      \tag{3}
\]

Using the packet's bounds \(|a|\leq36\), \(|j|\leq82\), this
gives \(|K|\leq249\), \(|[K,a]|\leq570\), and
\(|[K,b_1]|\leq500\), without expanding the shared words.

For every full canonical matrix microstate sequence, the corresponding
fixed word evaluations therefore satisfy

\[
\|[K_n,a_n]-I\|_2\longrightarrow0,\qquad
\|[K_n,b_{1,n}]-I\|_2\longrightarrow\sqrt2.       \tag{4}
\]

The first limit is a native relation. The second follows from (2)
and the canonical trace of that nonidentity word. This supplies a
specific bounded-word obstruction to the proposed double-centralizer
receiver.

The published root-definability results of
[Segal--Tent](https://ems.press/journals/jems/articles/6355057)
concern Chevalley groups over integral domains. Their coefficient
hypotheses do not cover this noncommutative Leavitt ring; (1)--(2)
show directly why the indicated conclusion would fail here. No
classification of \(C_H(C_H(a))\) is needed or asserted.

## 2. A native inner conjugation compresses the entire additive root

Define the following two matrices over \(R\):

\[
g=\begin{pmatrix}
s_0&0&s_1t_0\\
0&s_0&s_1t_{10}\\
0&0&t_{11}
\end{pmatrix},\qquad
g^{-1}=\begin{pmatrix}
t_0&0&0\\
0&t_0&0\\
s_0t_1&s_{10}t_1&s_{11}
\end{pmatrix}.                                   \tag{5}
\]

These are mutual inverses. Besides the elementary cancellations,
the bottom-right entry of \(g^{-1}g\) uses exactly the complete
prefix-code identity

\[
s_0t_0+s_{10}t_{10}+s_{11}t_{11}=1.
\]

The first column of \(g\) is \(s_0e_1\), and the second row of
\(g^{-1}\) is \(t_0e_2^T\). Hence, for every coefficient,

\[
g x_{12}(r)g^{-1}=x_{12}(\theta(r)),\qquad
\theta(r)=s_0rt_0.                               \tag{6}
\]

The map \(\theta\) is additive and injective, since
\(t_0\theta(r)s_0=r\). Its image is the proper corner
\(e_0Re_0\), where \(e_0=s_0t_0\). In particular

\[
gUg^{-1}\subsetneq U.
\]

Properness follows because \(1\notin e_0Re_0\): the complementary
projection \(s_1t_1\) is nonzero, as \(t_1(s_1t_1)s_1=1\).
This gives an actual global additive compression inside \(H\).
Its existence alone will not give a matrix-approximation obstruction.

### 2.1. Every nonzero finite additive window has an escaping root

There is no nonzero finite-dimensional \(\mathbb F_2\)-subspace
\(V\subset R\) with \(\theta(V)\subseteq V\). To verify the
only needed support fact, represent \(R\) on the algebraic vector
space with basis the non-eventually-periodic infinite binary strings.
The operators \(s_i\) prepend \(i\), while \(t_i\) delete an
initial \(i\), and give zero otherwise. This is a faithful unital
representation: the Leavitt relations hold, and faithfulness follows
from the established simplicity of \(R\) (equivalently, its
nonzero-element sandwich lemma).

Every element of \(\theta^n(R)\) has range in the span of strings
beginning with \(0^n\). The intersection of these spans is zero,
since the sole string beginning with every \(0^n\) is the excluded
eventually periodic string \(000\ldots\). Therefore

\[
\bigcap_{n\geq0}\theta^n(R)=\{0\}.               \tag{7}
\]

If a nonzero finite \(V\) were invariant, injectivity would make
\(\theta|_V\) bijective. It would put \(V\) in every
\(\theta^n(R)\), contradicting (7).

For a fixed such \(V\), choose \(r\in V\) with
\(\theta(r)\notin V\). In the canonical finite tracial algebra
\(L(H)\), the root unitary \(\lambda(x_{12}(\theta(r)))\) is
orthogonal to the entire finite Fourier algebra
\(L(x_{12}(V))\). Thus

\[
\operatorname{dist}_2\bigl(
 \lambda(gx_{12}(r)g^{-1}),L(x_{12}(V))\bigr)=1.   \tag{8}
\]

This is a fixed-window statement. It gives no uniform assertion for
coefficient windows chosen after inspecting a matrix microstate.

## 3. The one-root/one-compressor subsystem has explicit permutation models

Let \(G=\langle U,g\rangle\leq H\), and set

\[
A_\infty=\bigcup_{n\geq0}g^{-n}Ug^n.
\]

The union is increasing by (6), so it is an elementary abelian
two-group, hence locally finite. It is normalized by \(g\), and
\(G=A_\infty\langle g\rangle\). No nonzero power of \(g\)
lies in \(A_\infty\). Otherwise that power would centralize
\(U\), while (6) sends \(x_{12}(1)\) to
\(x_{12}(s_{0^n}t_{0^n})\ne x_{12}(1)\) for positive \(n\).
Consequently

\[
G\cong A_\infty\rtimes_\alpha\mathbb Z,
\qquad \alpha=\operatorname{Ad}(g)|_{A_\infty}.  \tag{9}
\]

Here is a direct finite-model construction, including the relevant
error estimate. Given finitely many lamps \(b_1',\ldots,b_q'\)
in \(A_\infty\), form the finite \(\mathbb F_2\)-space

\[
B_m=\operatorname{span}_{\mathbb F_2}
 \{\alpha^j(b_i'):\ |j|\leq m,\ 1\leq i\leq q\},
\qquad
F_m=\{a g^j:a\in B_m,\ -m\leq j\leq m\}.
\]

Right multiplication by every \(b_i'\) preserves \(F_m\), because
\((ag^j)b_i'=a\alpha^j(b_i')g^j\). Right multiplication by
\(g\) agrees with a cyclic shift of the second coordinate except
on its last level; the disagreement fraction is \(1/(2m+1)\).
The analogous statement holds for \(g^{-1}\).

Use these permutations, taking inverse right translations to obtain
the usual left-action multiplication convention. For a fixed word
of length \(\ell\), at most \(\ell/(2m+1)\) of the points see
one of the cyclic boundary modifications. Off those points its
evaluation is the actual free right action of the word on \(G\).
Thus an identity word has normalized permutation-matrix defect at
most

\[
\sqrt{\frac{2\ell}{2m+1}},                       \tag{10}
\]

while a nonidentity word has normalized trace tending to zero.
Increasing the finite lamp list gives canonical permutation
microstates for every fixed finite part of \(G\).

If the lamp list contains the native independent roots
\(x_{12}(s_0),x_{12}(t_0),x_{12}(v)\), their elementary abelian
group acts freely on every level, so its finite models are exact
regular multiples. The marked cycle \(c\), which moves between
root positions, is not supplied by this construction.

The full one-root/one-compressor relations are therefore compatible
with canonical finite permutation approximations, despite the proper
global inclusion in (6) and the fixed-window obstruction (8). A
negative proof must use additional native couplings. In particular,
the opposite-root relations of the full Steinberg system remain
outside this positive calibration; no sufficiency of any particular
additional packet is asserted.
