---
rg: 2
id: algebraic-cartan-pairs-effective-groupoid-algebras-citation
kind: route
title: Import of the algebraic Cartan pair reconstruction theorem of Armstrong, de Castro, Clark, Courtney, Lin, McCormick, Ramagge, Sims and Steinberg
target: algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras
requires: []
---

Source: Armstrong–de Castro–Clark–Courtney–Lin–McCormick–Ramagge–Sims–Steinberg, *Reconstruction of twisted Steinberg
algebras*, Int. Math. Res. Not. IMRN 2023, 2474–2542, doi:10.1093/imrn/rnab291. Read from the arXiv source of
arXiv:2101.08556 (`ACCCLMRSS.tex`), extracted on MSI (lane sk-rigidity-cartan, 2026-09-13). The line numbers refer to
that file.

**Normaliser, l.503–508 (`def:normaliser`):** "Let $R$ be a commutative unital ring, let $A$ be an $R$-algebra, and let
$B \subseteq A$ be a commutative $R$-subalgebra. Suppose that the set $I(B)$ of idempotents of $B$ is a set of
\emph{local units for $A$} [...] define the \emph{normaliser} of $B$ to be the set
$N(B) \coloneqq \{ n \in A : \text{there exists } k \in A \text{ with } knk = k, nkn = n, \text{and } kBn\cup nBk
\subseteq B \}$."

**Conditional expectation, l.596–606 (`def:conditional expectation`):** "A map $P\colon A \to B$ is called a
\emph{conditional expectation} if (i) $P$ is $R$-linear; (ii) $P\restr{B}=\id_B$; and (iii) $P(bab')=bP(a)b'$ for
$a\in A$ and $b, b'\in B$. The conditional expectation $P\colon A \to B$ is \emph{faithful} if, for every
$a \in A {\setminus} \{0\}$, there exists $n \in N(B)$ such that $P(n a) \ne 0$. The conditional expectation
$P\colon A \to B$ is \emph{implemented by idempotents} if, for every $n \in N(B)$, there exists $e \in I(B)$ such that
$P(n) = ne = en$."

**Pairs, l.615–628 (`def:ACP`):** "Let $R$ be a unital ring, let $A$ be an $R$-algebra, and let $B\subseteq A$ be a
commutative subalgebra satisfying~\cref{cond:torsion free} and with the following properties. (i) The set $I(B)$ forms
a set of local units for $A$. (ii) $B = \vecspan{(I(B))}$. (iii) $A = \vecspan{(N(B))}$. (iv) There exists a faithful
conditional expectation $P\colon A \to B$. Then we say that the pair $(A,B)$ is: (ADP) an \emph{algebraic diagonal pair}
if $A$ is spanned by the free normalisers of $B$; (ACP) an \emph{algebraic Cartan pair} if $B$ is a maximal commutative
subalgebra of $A$; and (AQP) an \emph{algebraic quasi-Cartan pair} if there is a faithful conditional expectation
$P\colon A \to B$ that is implemented by idempotents."

**Torsion condition, l.230:** "\Cref{cond:torsion free} holds automatically if $R$ is a field".

**l.659–661 (`lem:C=>Q`):** "Suppose that $(A,B)$ is an algebraic Cartan pair. Then $(A,B)$ is an algebraic quasi-Cartan
pair, and every conditional expectation $P\colon A \to B$ is implemented by idempotents."

**l.1087–1089 (`prop:Hausdorff`):** "Suppose that $(A,B)$ is an algebraic quasi-Cartan pair. Then $G$ is Hausdorff."

**l.1312–1314 (`thm:main`):** "Suppose that $(A,B)$ is an algebraic quasi-Cartan pair. Let $G$ and $\Sigma$ be the
groupoids constructed in \cref{sec:build twist}. Then the map $\varphi\colon a \mapsto \widehat{a}$ from $A$ to
$C(\Sigma,R)$ defined in \cref{prop:ahat} is an isomorphism of $A$ onto $A_R(G;\Sigma)$ that takes $B$ to
$A_R(\Go; q^{-1}(\Go))$, which is isomorphic to $A_R(\Sigmao)$, and hence also to $A_R(\Go)$."

**`prop:effective`:** "Suppose that $(A,B)$ is an algebraic quasi-Cartan pair. Then (a) $(A,B)$ is an algebraic Cartan
pair if and only if $G$ is effective, and (b) $(A,B)$ is an algebraic diagonal pair if and only if $G$ is principal."

**l.891–893 (`prop:effectiveACPprincipalADP`):** "Let $R$ be an indecomposable commutative ring and let
$(\Sigma,i,q)$ be a discrete $R$-twist over an ample Hausdorff groupoid $G$. If $G$ is effective then
$(A,B) \coloneqq (A_R(G;\Sigma), A_R(\Go; q^{-1}(\Go)))$ is an algebraic Cartan pair, and if $G$ is principal then
$(A,B)$ is an algebraic diagonal pair."

**l.1589–1596 (`cor:equiv.twist.effective`):** "Let $(\Sigma_1,i_1,q_1)$ and $(\Sigma_2,i_2,q_2)$ be discrete $R$-twists
over ample Hausdorff groupoids $G_1$ and $G_2$, respectively. Suppose that $G_1$ is effective. The following are
equivalent. (1) The twists [...] are isomorphic. (2) There exists a diagonal-preserving isomorphism of $R$-algebras
$\Psi\colon A_R(G_1;\Sigma_1)\to A_R(G_2;\Sigma_2)$. (3) There exists an isomorphism of $R$-algebras [...] such that
$\Psi\big(A_R(G^{(0)}_1; q_1^{-1}(G^{(0)}_1))\big) \subseteq A_R(G^{(0)}_2; q_2^{-1}(G^{(0)}_2))$."

**Remark (3) after `def:ACP`:** "So the corresponding questions of existence and uniqueness of algebraic quasi-Cartan
subalgebras in a given $R$-algebra are natural and interesting questions, though they are not addressed in this paper."

These quotes give the target claim.
