---
rg: 2
id: strict-kazhdan-compressor-kazhdan-projection-proof
kind: route
title: Detect the finite-dimensional radical with the difference of two Kazhdan projections
target: strict-kazhdan-compressor-forces-non-rfd
requires:
  - commutant-no-growth
---

# Strict Kazhdan compression produces an RFD radical projection

Let \(H\leq G\) have property \((T)\), let
\[
                     K=tHt^{-1}<H,                       \tag{1}
\]
and write \(C^*(L)=C^*_{\max}(L)\) for every group \(L\).

## 1. The Kazhdan projection embeds in the ambient full algebra

Property \((T)\) gives a Kazhdan projection
\[
                     p_H\in C^*(H):                      \tag{2}
\]
for every unitary representation \(\pi\) of \(H\),
\(\pi(p_H)\) is the orthogonal projection onto
\(\operatorname{Fix}_\pi(H)\).

The canonical map \(C^*(H)\to C^*(G)\) is injective.  One quick proof is
induction: every unitary representation of \(H\) embeds in the restriction
to \(H\) of its induced representation on \(G\).  Hence the full
\(C^*\)-norm of an element of \(\mathbb C[H]\) is unchanged when it is
viewed in \(\mathbb C[G]\).

Regard \(p=p_H\) as a projection of \(C^*(G)\), and set
\[
                     q=tpt^{-1}.                         \tag{3}
\]
In a unitary representation \(\pi\) of \(G\), \(\pi(q)\) is the
orthogonal projection onto \(\operatorname{Fix}_\pi(K)\).

## 2. Inclusion plus equal finite rank kills the difference

Since \(K\leq H\), every representation \(\pi\) of \(G\) satisfies
\[
 \operatorname{Fix}_\pi(H)\subseteq\operatorname{Fix}_\pi(K),
 \qquad \pi(p)\leq\pi(q).                                 \tag{4}
\]
Apply this to a faithful universal representation of \(C^*(G)\).  It
follows that \(p\leq q\) in \(C^*(G)\), and therefore
\[
                     e=q-p                               \tag{5}
\]
is a projection.

Now let \(\pi:G\to U(n)\) be finite-dimensional.  Equation (3) says
\[
          \pi(q)=\pi(t)\pi(p)\pi(t)^*,
\]
so \(\pi(p)\) and \(\pi(q)\) have the same finite rank.  Together with
(4), this forces
\[
                     \pi(p)=\pi(q),\qquad \pi(e)=0.       \tag{6}
\]
Thus \(e\) lies in the kernel of every finite-dimensional representation.

## 3. A quasi-regular vector proves that the projection is nonzero

Let \(\sigma\) be the quasi-regular representation of \(G\) on
\(\ell^2(G/K)\), and let \(\delta_K\) be the root coset vector.  It is
fixed by \(K\), so
\[
                     \sigma(q)\delta_K=\delta_K.          \tag{7}
\]
It is not fixed by \(H\): choose \(h\in H\setminus K\), and then
\(hK\ne K\).  Hence
\[
                     \sigma(p)\delta_K\ne\delta_K.        \tag{8}
\]
Equations (7)--(8) imply
\[
                     \sigma(e)\delta_K\ne0,               \tag{9}
\]
so \(e\ne0\) in \(C^*(G)\).  Equations (6) and (9) prove that
\(C^*(G)\) is not RFD.

There is a uniform coefficient gap.  Put \(n=[H:K]\), allowing
\(n=\infty\), and use the convention \(1/\infty=0\).  The \(H\)-orbit
of \(K\) is \(H/K\).  Projection of its root vector onto the constant
vectors gives
\[
 \langle \sigma(p)\delta_K,\delta_K\rangle={1\over n}.
\]
Consequently
\[
 \langle \sigma(e)\delta_K,\delta_K\rangle
       =1-{1\over n}\ge {1\over2}.                        \tag{10}
\]
The inequality uses strictness: \(n\ge2\).

## 4. A fixed finite group-algebra polynomial witnesses the gap

The exact radical projection need not be finitely supported, but it has
uniformly quantitative finite-support approximants.

Choose a finite symmetric Kazhdan set \(Q\) for \(H\), put \(m=|Q|\),
and use the convention
\[
 \operatorname{dist}(\xi,\operatorname{Fix}_\pi(H))
 \leq {1\over\kappa}\max_{s\in Q}\|\pi(s)\xi-\xi\|.        \tag{11}
\]
Define the normalized Kazhdan Laplacian
\[
 \Delta={1\over m}\sum_{s\in Q}(1-s)^*(1-s)\in\mathbb C[H].
                                                                    \tag{12}
\]
It is a positive contraction after division by \(4\), and (11) gives
the universal spectral gap
\[
 \operatorname{Spec}(\Delta)\subseteq
 \{0\}\cup[c,4],\qquad c={\kappa^2\over m}.               \tag{13}
\]
The Kazhdan projection is \(p=1_{\{0\}}(\Delta)\).  For \(N\ge1\), put
\[
 p_N=\left(1-{\Delta\over4}\right)^N\in\mathbb C[H],
 \qquad
 e_N=t p_Nt^{-1}-p_N\in\mathbb C[G].                     \tag{14}
\]
If
\[
             \theta=1-{\kappa^2\over4m}<1,                \tag{15}
\]
functional calculus gives
\[
 \|p_N-p\|\leq\theta^N,\qquad
 \|e_N-e\|\leq2\theta^N.                                  \tag{16}
\]
The support of \(p_N\) consists of \(Q\)-words of length at most \(N\);
thus \(e_N\) is one fixed finite linear combination of words of length at
most \(N+2\) in \(Q\cup\{t,t^{-1}\}\).

For every finite-dimensional representation \(\pi\), equation (6) and
(16) imply the uniform operator-norm estimate
\[
                   \|\pi(e_N)\|\leq2\theta^N.             \tag{17}
\]
On the other hand, (10) and (16) give
\[
 \langle\sigma(e_N)\delta_K,\delta_K\rangle
       \geq {1\over2}-2\theta^N.                          \tag{18}
\]
Equivalently, for every \(0<\varepsilon<1/4\), any
\[
 N\geq
 {\,\log(2/\varepsilon)\,\over-\log(1-\kappa^2/(4m))}     \tag{19}
\]
satisfies
\[
 \sup_{\dim\pi<\infty}\|\pi(e_N)\|\leq\varepsilon,
 \qquad
 \|e_N\|_{C^*(G)}\geq
 \langle\sigma(e_N)\delta_K,\delta_K\rangle
 \geq {1\over2}-\varepsilon.                             \tag{20}
\]
Thus a finite word-polynomial already separates the full norm from every
finite-dimensional norm by a fixed amount.  Passing \(N\to\infty\)
recovers the exactly invisible projection \(e\).

## 5. Why this is not a reduced-trace root witness

Strict inclusion between conjugate groups forces \(H\) to be infinite.
The restriction of the left regular representation of \(G\) to \(H\) is
a direct sum of regular \(H\)-representations, so it has no nonzero
\(H\)-invariant vectors.  Therefore
\[
       \lambda_G(p)=\lambda_G(q)=\lambda_G(e)=0.           \tag{21}
\]
In particular the canonical reduced trace kills the exact projection
\(e\).  Moreover (16) gives
\[
       \|\lambda_G(e_N)\|\leq2\theta^N.                   \tag{22}
\]

The obstruction is consequently a maximal-C-star and finite-dimensional
stability obstruction.  It does not supply a nonzero canonical-trace
projection, a regular root, or evidence that \(G\) is nonhyperlinear.
Indeed \(G\) may still be residually finite, sofic, and hyperlinear as a
group.  What fails is the RFD/Fell-density input needed to replace a
prescribed matrix microstate by finite-dimensional exact actor
representations.
