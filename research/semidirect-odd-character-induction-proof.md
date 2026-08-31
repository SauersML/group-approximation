---
rg: 2
id: semidirect-odd-character-induction-proof
kind: route
title: Induce every odd torsor character through the finite action quotient
target: conjugacy-actions-cannot-prune-the-odd-tv-spectrum
requires:
  - tv-zero-noise-cell-is-an-abelian-torsor
---

# Induce every odd torsor character through the finite action quotient

## 1. The action always has finite image

Let

$$
H\cong(C_2)^P
$$

and let

$$
\alpha:K\longrightarrow\operatorname{Aut}(H)           \tag{1}
$$

be an arbitrary action with \(\alpha(k)(z)=z\) for all \(k\in K\).  Put

$$
A:=\alpha(K).                                           \tag{2}
$$

The group \(H\) is finite, so \(\operatorname{Aut}(H)\) and \(A\) are
finite.  There is a quotient homomorphism

$$
q:H\rtimes_\alpha K\longrightarrow H\rtimes A,
\qquad
q(h,k)=(h,\alpha(k)).                                  \tag{3}
$$

It preserves the entire copy of \(H\).  In particular, it preserves
\(J=(z,1)\).

Thus it is enough to construct the required representation for the finite
semidirect product \(H\rtimes A\).

## 2. Explicit induced representation

Fix a character

$$
\chi:H\longrightarrow\{+1,-1\}.                        \tag{4}
$$

On the finite-dimensional Hilbert space \(\ell^2(A)\), with basis
\(\{e_a:a\in A\}\), define

$$
\rho_\chi(h)e_a
 :=\chi(a^{-1}\mathbin{\cdot}h)e_a,
\qquad
\rho_\chi(b)e_a
 :=e_{ba}                                               \tag{5}
$$

for \(h\in H\) and \(a,b\in A\).  The first family is diagonal and the
second is the left regular permutation representation.

For \(b\in A\),

$$
\begin{aligned}
\rho_\chi(b)\rho_\chi(h)\rho_\chi(b)^{-1}e_a
 &=\chi(a^{-1}b\mathbin{\cdot}h)e_a \\
 &=\rho_\chi(b\mathbin{\cdot}h)e_a.
\end{aligned}                                          \tag{6}
$$

Therefore (5) respects the semidirect-product relation and defines a
unitary representation of \(H\rtimes A\).  It is the usual induced
representation from \(\chi\), written without choosing orbit
representatives.

At the basis vector \(e_1\), the restriction to \(H\) acts by \(\chi\).
Hence \(\chi\) occurs in the joint spectrum of
\(\rho_\chi|_H\).

Because every \(a\in A\) fixes \(z\),

$$
\rho_\chi(z)e_a
 =\chi(a^{-1}\mathbin{\cdot}z)e_a
 =\chi(z)e_a.                                          \tag{7}
$$

Thus

$$
\rho_\chi(z)=\chi(z)I.                                 \tag{8}
$$

If \(\chi(z)=-1\), composing (5) with the quotient (3) gives a
finite-dimensional representation of \(H\rtimes K\) in which \(J=-I\).

## 3. Application to the zero-noise TV torsor

For a zero-noise Taller--Vidick cell, the prerequisite elimination gives

$$
H\cong\{+1,-1\}^{P}.
$$

Its characters are indexed by subsets \(\beta\subseteq P\):

$$
\chi_\beta(h)=\prod_{p\in\beta}h(p),
\qquad
\chi_\beta(z)=(-1)^{|\beta|}.                           \tag{9}
$$

Every odd \(\beta\), including every \(|\beta|\geq3\), therefore satisfies
the hypothesis of Section 2.  The representation
\(\rho_{\chi_\beta}\) is finite-dimensional, has \(J=-I\), and contains
the bad joint spectral atom \(\chi_\beta\).

The conclusion does not depend on how the action permutes weights.  An
orbit can mix singleton and high-degree characters; the induced
representation then contains the whole orbit and still contains the bad
atom.  An orbit can consist only of high-degree characters; it still gives
a finite-dimensional sector by the same construction.

## 4. Exact boundary of the argument

The presentation in this theorem has only two kinds of relations:

1. relations internal to \(H\) and internal to \(K\);
2. conjugacy relations implementing the action \(\alpha\).

Those are exactly the relations of a split extension \(H\rtimes K\).
They include arbitrarily noncommuting conjugators and arbitrarily many
conjugacy cycles.

A relation equating a word in the conjugators to a nontrivial element of
\(H\), or a more general nonsplit extension relation, need not factor
through (3).  Likewise, a joint spectral-projector relation is not a group
relation at all.  These are outside the theorem.

There is still a sharp finite fence: if the enlarged auxiliary group is
itself finite, contains \(H\), and keeps \(z\) central as the marked sign,
then the ordinary finite-dimensional induced representation \(\operatorname{Ind}_H^G\chi\) exists for every
\(\chi\), split or not.  Hence a nonsplit escape capable of eliminating all
bad finite-dimensional sectors must already be an infinite extension in
which the marked finite subgroup \(H\) fails to survive in the relevant
finite-dimensional representations.  Producing that failure is no easier
than the relative representation-separation problem sought by the main
project.
