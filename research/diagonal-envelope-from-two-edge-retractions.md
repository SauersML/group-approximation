---
rg: 2
id: diagonal-envelope-from-two-edge-retractions
kind: route
title: Synchronize two split edges in the direct-product envelope
target: split-edge-asymmetric-amalgams-are-operator-mf
requires:
  - common-mf-envelope-fences-asymmetric-amalgams
---

# Synchronize two split edges in the direct-product envelope

## 1. Direct products preserve operator MF

Suppose \(G_i\) embeds in the unitary group of a norm matrix corona
\[
\mathcal Q_i=\prod_n M_{d_{i,n}}\big/\bigoplus_n M_{d_{i,n}}
\qquad(i=0,1).
\]
After harmless reindexing, block sum gives an injective C*-homomorphism
\[
\mathcal Q_0\oplus\mathcal Q_1
\longrightarrow
\prod_n M_{d_{0,n}+d_{1,n}}\big/
\bigoplus_n M_{d_{0,n}+d_{1,n}}.                         \tag{1}
\]
It is injective because the norm of a block diagonal matrix is the maximum
of the two block norms. Composing the two group embeddings with (1) gives
\[
(g_0,g_1)\longmapsto \phi_0(g_0)\oplus\phi_1(g_1).       \tag{2}
\]
Equation (2) is a homomorphism, and it is injective because a nonidentity
component stays nonidentity in its block. Hence \(G_0\times G_1\) is
operator MF.

## 2. The diagonal common envelope

Put \(M=G_0\times G_1\) and define \(j_0,j_1\) by (SER3). They are
homomorphisms. Each is injective because its first, respectively second,
coordinate is the original element.

For \(h\in H\), the retraction identities give
\[
\begin{aligned}
j_0\theta_0(h)
 &=\bigl(\theta_0(h),\theta_1r_0\theta_0(h)\bigr)
  =\bigl(\theta_0(h),\theta_1(h)\bigr),\\
j_1\theta_1(h)
 &=\bigl(\theta_0r_1\theta_1(h),\theta_1(h)\bigr)
  =\bigl(\theta_0(h),\theta_1(h)\bigr).                  \tag{3}
\end{aligned}
\]
Thus the two unequal vertices satisfy the synchronized-envelope hypothesis
(CME1) inside the operator-MF group \(M\).
The claim **common-mf-envelope-fences-asymmetric-amalgams** now gives an
injection
\[
G_0*_H G_1\hookrightarrow
M*_{\{(\theta_0(h),\theta_1(h)):h\in H\}}M
\]
and operator MF of the source.

## 3. Terminal-sign consequence

Every semidirect-product vertex \(N\rtimes H\) has the canonical retraction
\((n,h)\mapsto h\). Therefore changing kernels, making the two kernels
nonisomorphic, or putting property \((T)\) on \(H\) does not evade the
firewall if both vertices retain split projections to the edge.

There is also a quick certificate that a proposed actor vertex does evade
this particular theorem. Let \(c\in H\), suppose a finite quotient
\(q:H\to F\) has \(q(c)\ne1\), and suppose every finite-dimensional unitary
representation of an actor vertex \(D\) kills \(\theta(c)\). If
\(r:D\to H\) retracted \(\theta\), then
\[
D\xrightarrow{r}H\xrightarrow{q}F
\]
followed by the faithful left-regular representation of \(F\) would be a
finite-dimensional representation of \(D\) detecting \(\theta(c)\), a
contradiction.

This proves only that the actor edge is non-split. It does not prove failure
of Shulman's broader compatible-corona condition, and it supplies no
normalized-Hilbert--Schmidt collapse. Those are the two remaining asymmetric
gates.
