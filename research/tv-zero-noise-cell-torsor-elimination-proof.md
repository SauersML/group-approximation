---
rg: 2
id: tv-zero-noise-cell-torsor-elimination-proof
kind: route
title: Eliminate one zero-noise Taller--Vidick cell to an abelian torsor
target: tv-zero-noise-cell-is-an-abelian-torsor
requires: []
---

# Eliminate one zero-noise Taller--Vidick cell to an abelian torsor

## 1. Relations surviving at epsilon zero

In [Taller--Vidick Definition
4.1](https://arxiv.org/html/2507.22444v2#S4), the test samples functions
\(f\) on the \(U\)-assignment cube, \(g\) on the \(W\)-assignment cube, and
an independent mask \(\mu\), then sets

$$
g'=f^\uparrow g\mu.                                    \tag{1}
$$

At \(\epsilon=0\), the Bernoulli mask is identically one.  Thus the support
contains exactly the equations with

$$
g'=f^\uparrow g.                                       \tag{2}
$$

Fix one outer tuple \((W,U,C)\).  Let \(S\) be the nonempty set of
\(W\)-assignments satisfying \(C\).  A conditioned signed \(W\)-query
depends only on the restriction of \(g\) to \(S\).  Since \(g\) ranges over
all functions on the full assignment cube, its effective index group is

$$
K:=\{+1,-1\}^{S}                                       \tag{3}
$$

with pointwise multiplication.

A lifted \(U\)-query restricts to a function on \(S\) which depends only on
\(y|_U\).  Let \(H\leq K\) be the image of this restriction map.  Equivalently,
if

$$
P:=\{y|_U:y\in S\},
$$

then

$$
H\cong\{+1,-1\}^{P}.                                   \tag{4}
$$

Write \(z\in H\) for the constant-minus-one function.

## 2. Absorb all folding signs

For a sign \(\sigma\in\{+1,-1\}\), write
\([\sigma]=1\) for \(\sigma=+1\) and \([\sigma]=J\) for
\(\sigma=-1\).  If \(x_{U,s_U(f)}\) and \(x_{W,s_{g,C}}\) are the raw
solution-group generators, define signed generators

$$
A_f:=[m_f]x_{U,s_U(f)},
\qquad
B_g:=[m_{g,C}]x_{W,s_{g,C}}.                            \tag{5}
$$

The raw parity equation has right-hand side
\([m_fm_{g,C}m_{f^\uparrow g,C}]\).  Multiplying its three variables by the
same sign factors in (5) cancels that right-hand side.  Hence (2) becomes

$$
A_fB_gB_{f^\uparrow g}=1.                              \tag{6}
$$

The three factors in (6) commute because they form one LCS context.

Folding over true gives

$$
A_{-f}=JA_f,
\qquad
B_{-g}=JB_g.                                           \tag{7}
$$

If two lifted \(U\)-queries have the same image \(h\in H\), then their third
\(B\)-indices agree in (6) for every \(g\), so (6) identifies their
\(A\)-generators.  Likewise, conditioning identifies \(B\)-generators with
the same \(k\in K\).  We may therefore write \(A_h,B_k\), and the complete
cell relations are

$$
A_hB_kB_{hk}=1
\qquad(h\in H,\ k\in K),                               \tag{8}
$$

with the context commutations and involution relations.  Equation (7)
becomes

$$
A_z=J,
\qquad
B_{zk}=JB_k.                                           \tag{9}
$$

The second identity in (9) will follow from (8) and the first.

## 3. The A-generators form exactly H

Put \(h=1\) in (8).  Since \(B_k^2=1\),

$$
A_1=1.                                                  \tag{10}
$$

Because the factors in (8) commute and are involutions, solve (8) for its
last factor:

$$
B_{hk}=B_kA_h.                                         \tag{11}
$$

In particular, \(A_h\) commutes with every \(B_k\).

For \(h_1,h_2\in H\), compute \(B_{h_1h_2k}\) in two ways:

$$
B_{h_1h_2k}
 =B_{h_2k}A_{h_1}
 =B_kA_{h_2}A_{h_1},
$$

whereas (11) applied once gives

$$
B_{h_1h_2k}=B_kA_{h_1h_2}.
$$

Cancel \(B_k\).  Therefore

$$
A_{h_1h_2}=A_{h_1}A_{h_2}.                             \tag{12}
$$

Thus \(h\mapsto A_h\) is a homomorphism from the elementary abelian group
\(H\), and all \(A_h\) commute.  The folding relation is precisely
\(A_z=J\).

## 4. One free involution per H-coset

Choose a transversal \(Q\subseteq K\) for the cosets \(K/H\), and define

$$
T_q:=B_q
\qquad(q\in Q).
$$

Every \(k\in K\) has a unique form \(k=hq\), and (11) says

$$
B_{hq}=T_qA_h.                                         \tag{13}
$$

Each \(T_q\) is an involution and commutes with every \(A_h\).  The defining
relations never connect two different \(H\)-cosets, so no relation between
distinct \(T_q\)'s should remain.  To verify this without relying on
presentation intuition, define

$$
D:=H\times\left(*_{q\in Q}\langle t_q\mid t_q^2=1\rangle\right).       \tag{14}
$$

There is a homomorphism from the cell group to \(D\) given by

$$
A_h\longmapsto(h,1),
\qquad
B_{hq}\longmapsto(h,t_q),
\qquad
J\longmapsto(z,1).                                      \tag{15}
$$

Indeed, for \(k=h_0q\), the image of the left side of (8) is

$$
(h,1)(h_0,t_q)(hh_0,t_q)=(1,1),
$$

and its three factors commute.  Conversely, send \(h\in H\) to \(A_h\) and
\(t_q\) to \(T_q=B_q\).  Equations (12) and (13) show this is a homomorphism
and that the two maps are inverse.  Hence

$$
\boxed{\Gamma_{\rm cell}
 \cong H\times\left(*_{q\in K/H}C_2\right)}.            \tag{16}
$$

Under (16), \(J=(z,1)\).

## 5. Scalar profiles and finite-dimensional detection

The finite elementary abelian group \(H\cong\{+1,-1\}^{P}\) has one
character for every subset \(\beta\subseteq P\):

$$
\chi_\beta(h)=\prod_{p\in\beta}h(p).                    \tag{17}
$$

Since \(z(p)=-1\) for every \(p\),

$$
\chi_\beta(z)=(-1)^{|\beta|}.                           \tag{18}
$$

Therefore the scalar \(A\)-profiles with \(J=-1\) are exactly the odd
subsets \(\beta\).  There are \(2^{|P|-1}\).  Singleton subsets are the
honest dictator evaluations; every odd subset of size at least three is a
nondictator.  Each such \(A\)-profile extends to the full cell by assigning
an arbitrary scalar sign to every free involution \(T_q\).

The free product of finitely many finite groups is virtually free and
residually finite.  Its direct product with finite \(H\) is residually
finite as well.  In particular, not only \(J\) but every nontrivial local
word is visible in some finite-dimensional representation.

Thus epsilon zero removes the positive-noise contradiction but leaves an
exact elementary-abelian torsor, with all odd characters undamped.  Only
identifications between different outer cells can possibly remove those
characters or create an infinite-versus-finite representation gap.
