# Relative cut costs can accumulate for exact expectations

Date: 2026-09-08.

This elementary example tests recursive extraction of a finite algebra
by low-energy projection cuts. Arbitrarily small relative costs at each
split do not bound the final aggregate cost, even when the original
channel and every normalized corner channel are exact expectations.
It is not a counterexample to uniform conditional-expectation rounding.

Throughout, traces are normalized. For a self-adjoint bistochastic UCP
map \(P\), write

\[
\mathcal E_P(x)=\tau(x^*(I-P)x).
\]

## 1. Exact tensor calculation

Let \(D_2\subset M_2\) be the diagonal algebra in the Pauli \(Z\)
basis. For \(k\geq1\), put

\[
M=M_2^{\otimes k},\qquad D=D_2^{\otimes k},\qquad P=E_D.
\]

Fix \(0<\theta<\pi/4\), and set

\[
r=\cos\theta\,Z+\sin\theta\,X,\qquad
e_\pm=\frac{1\pm r}{2},\qquad
a=\frac{1+\cos^2\theta}{2}=1-\frac{\sin^2\theta}{2}.
\]

The \(e_\pm\) are orthogonal rank-one projections. Directly,

\[
e_\pm E_{D_2}(e_\pm)e_\pm=a e_\pm,
\qquad \tau_2(e_\pm)=\frac12.
\]

For a prefix \(\sigma\in\{+,-\}^{\ell}\), define

\[
p_\sigma=e_{\sigma_1}\otimes\cdots\otimes e_{\sigma_\ell}
             \otimes1^{\otimes(k-\ell)}.
\]

The empty prefix has projection one. For every prefix,

\[
\tau(p_\sigma)=2^{-\ell},\qquad
\tau(p_\sigma P(p_\sigma))=2^{-\ell}a^\ell,
\qquad
\mathcal E_P(p_\sigma)=2^{-\ell}(1-a^\ell).       \tag{1}
\]

Split a length-\(\ell\) parent \(p=p_\sigma\) into
\(q_\pm=p_{\sigma\pm}\). Both children have half its trace, and

\[
\frac{\mathcal E_P(q_+)+\mathcal E_P(q_-)-\mathcal E_P(p)}
     {\min\{\tau(q_+),\tau(q_-)\}}
 =2a^\ell(1-a)\leq\sin^2\theta.                 \tag{2}
\]

Thus every split has small relative boundary increment, independently
of the recursion depth.

### 1.1. The normalized corner channels are also exact

Identify \(p_\sigma M p_\sigma\) with \(M_2^{\otimes(k-\ell)}\)
by its rank-one initial tensor factor, and equip it with trace
\(\tau(\cdot)/\tau(p_\sigma)\). On this corner,

\[
p_\sigma P(\,\cdot\,)p_\sigma
       =a^\ell E_{D_2^{\otimes(k-\ell)}}.
\]

Consequently the correctly normalized map

\[
Q_\sigma(\,\cdot\,)
   =a^{-\ell}p_\sigma P(\,\cdot\,)p_\sigma
\]

is an exact trace-preserving conditional expectation. Without the
factor \(a^{-\ell}\), the compressed map is not unital.
For either next child, its relative energy measured in this normalized
corner is

\[
\frac{\mathcal E_{Q_\sigma}(q_\pm)}
     {\min\{\tau_{p_\sigma}(q_\pm),
             \tau_{p_\sigma}(p_\sigma-q_\pm)\}}
 =1-a=\frac{\sin^2\theta}{2}.                    \tag{3}
\]

Thus the failure persists for a rule using relative energy in a
normalized corner, with zero idempotence defect in every such corner.

## 2. The terminal partition can be far from the correct algebra

At depth \(k\), the projections \(p_\sigma\) form a rank-one partition
of one. Let \(B\) be their generated MASA. Equation (1) gives

\[
\sum_{|\sigma|=k}\mathcal E_P(p_\sigma)=1-a^k.   \tag{4}
\]

There is also a uniform-unit-ball witness. The unitary
\(u=r^{\otimes k}\) belongs to \(B\), while
\(P(u)=\cos^k\theta\,Z^{\otimes k}\). Since \(P\) is the
orthogonal projection in \(L^2\),

\[
\|P-E_B\|_{\infty\to2}
 \geq\|P(u)-u\|_2
 =\sqrt{1-\cos^{2k}\theta}.                     \tag{5}
\]

Choose \(\theta_n\to0\) and \(k_n\sin^2\theta_n\to\infty\).
Every local cost in (2)--(3) tends to zero, but both (4) and the
lower bound in (5) tend to one. The correct exact expectation is
still \(P=E_D\).

### 2.1. Strictly positive vanishing defects do not fix this cut rule

For \(0<\varepsilon<1\), instead take

\[
P_\varepsilon=(1-\varepsilon)E_D+\varepsilon\,\mathrm{id}.
\]

It is self-adjoint and bistochastic UCP, and

\[
\|P_\varepsilon^2-P_\varepsilon\|_{\infty\to2}
 =\varepsilon(1-\varepsilon).
\]

Here \(\|\mathrm{id}-E_D\|_{\infty\to2}=1\), attained by an
off-diagonal Pauli unitary. All global energies in (1)--(2) gain the
factor \(1-\varepsilon\), while

\[
\|P_\varepsilon-E_B\|_{\infty\to2}
 \geq(1-\varepsilon)\sqrt{1-\cos^{2k}\theta}.
\]

For any strictly positive cut-tolerance function of the actual defect,
choose \(\sin^2\theta\) below that tolerance and then take \(k\)
sufficiently large. As \(\varepsilon\to0\), all permitted local
relative costs can vanish while this lower bound tends to one.

More precisely, the prefix compression has unitalizing factor
\(b_\ell=(1-\varepsilon)a^\ell+\varepsilon\). Its normalized map is

\[
(1-\varepsilon_\ell)E_{D_2^{\otimes(k-\ell)}}
       +\varepsilon_\ell\mathrm{id},\qquad
\varepsilon_\ell=\frac{\varepsilon}{b_\ell}.
\]

Each next local relative energy is
\((1-\varepsilon_\ell)(1-a)\leq1-a\). The normalized corner's
idempotence defect, however, can become order one when
\(a^\ell\) is comparable to \(\varepsilon\). The original small
defect alone does not preserve a small-defect hypothesis throughout
this perturbed recursion.

## 3. What this rules out, and what it does not

An unrestricted recursion based only on local relative cut costs,
or on their relative increments, cannot infer a small final aggregate
cost from uniform near-idempotence. Equations (1)--(5) are an exact
countermodel to that inference.

A rule imposing a global energy bound on every terminal projection
avoids this example. For the exact channel and any nonempty prefix,

\[
\frac{\mathcal E_P(p_\sigma)}
     {\min\{\tau(p_\sigma),\tau(1-p_\sigma)\}}
 =1-a^{|\sigma|}.
\]

Requiring this ratio to be at most \(h\) stops the displayed recursion
before \(1-a^{|\sigma|}>h\). More generally, if an orthogonal partition
\((p_i)\) satisfies \(\mathcal E_P(p_i)\leq h\tau(p_i)\) for every
leaf, then \(\sum_i\mathcal E_P(p_i)\leq h\). This is a genuine global
budget, rather than a consequence of the local rules tested above.

The unresolved extraction step is to obtain a sufficiently informative
partition, and compatible matrix blocks, while preserving such a global
budget or an equivalent uniform repair estimate. This example does not
exclude that possibility and gives no obstruction to rounding the
channels themselves: \(P_\varepsilon\) is already within
\(\varepsilon\) of \(E_D\) in \(\infty\to2\) norm.
