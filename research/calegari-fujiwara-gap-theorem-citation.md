---
rg: 2
id: calegari-fujiwara-gap-theorem-citation
kind: route
title: Import Theorem A-prime, the no-mirrors remark and Bavard duality from Calegari--Fujiwara
target: calegari-fujiwara-gap-theorem-strong-version
requires: []
---

Quoted verbatim from arXiv:math/0611889 (`wordstable0.28.tex`, fetched on MSI into
`/scratch.global/sauer354/hl-zd-amplification/src/math_0611889/`).

(1) **Theorem A′, l.256–280.** "\begin{improved_gap_thm}[Gap Theorem, strong version]
Let $G$ be a word-hyperbolic group that is $\delta$-hyperbolic with respect to a
symmetric generating set $S$ with $|S|$ generators. Let $a \in G$ be a (non-torsion)
element. Assume there is no $n >0$ and no $b \in G$ with $ba^{-n}b^{-1}=a^n$. Then
there is a homogeneous quasimorphism $h$ on $G$ such that \begin{enumerate}
\item{$h(a) =1 $} \item{The defect of $h$ is $\le C(\delta,|S|)$.} \end{enumerate}"
The theorem continues with a relative version, not used here.

(2) **Remark, l.696–705.** "If $ba^{-n}b^{-1} = a^n$ for some $b$ and positive integer
$n$, then $b^2$ and $a^n$ commute, and since $G$ is hyperbolic, suitable powers of $a$
and $b$ generate an infinite dihedral group. It follows that if $G$ is torsion free, no
such element $b$ can exist."

(3) **Bavard duality, l.545–548.** "Let $G$ be a group. Then for any $a \in [G,G]$, we
have an equality $$\scl(a) = \frac 1 2 \sup_{\phi \in Q(G)} \frac {|\phi(a)|}
{D(\phi)}$$", with l.551–552: "one must take the supremum over $\phi \in Q(G)$ with
$\phi(a)\ne 0$ (and therefore $D(\phi)>0$) for this to make sense".

**Deduction.** In a torsion-free group a nontrivial element is non-torsion, and by (2)
no `b`, `n` as in (1) exist, so (1) applies. For the consequence, `h(a) = 1` with
`a in [G,G]` forces `h` not to be a homomorphism, hence `D(h) > 0`, and (3) gives
`scl(a) >= |h(a)| / (2 D(h)) > 0`.
