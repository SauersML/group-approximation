---
rg: 2
id: oos-graded-small-cancellation-scales-separate-citation
kind: route
title: Import Definition classQ, Definition SC and Lemma asc of Olshanskii--Osin--Sapir
target: oos-graded-small-cancellation-scales-separate
requires: []
---

Literature import. A. Yu. Olshanskii, D. V. Osin, M. V. Sapir, *Lacunary hyperbolic groups*,
Geom. Topol. 13 (2009), 2051--2140, arXiv:math/0701365.

**Verification boundary.** The arXiv e-print source (`oos72.tex`) was read on 2026-09-19. The
passages below are copied verbatim from it, including the TeX macros. The only changes are that
the `\begin{...}`, `\end{...}` and `\item[...]` markup has been removed (item labels are kept) and
that some line breaks have been rejoined. In that source,
`\qq` is `{\mathcal Q}`, `\calr` is `\mathcal R`, `\ch` expands to "lacunary hyperbolic" and
`\gsc` expands to "graded small cancellation".

**Injectivity radius** (before Theorem `dl2`, and again before Theorem `dirlim`):

> Let $\alpha\colon G\to G'$ be a homomorphism, $G=\la S\ra$. The {\em
> injectivity radius} of $\alpha$ is the maximal radius of a ball in
> the Cayley graph $\Gamma(G,S)$ where $\alpha$ is injective.

> we denote by $r_S(\alpha )$ the {\it injectivity radius of
> $\alpha $ with respect to $S$}, i.e., the radius of the largest ball
> $B$ in $G$ such that $\alpha $ is injective on $B$.

**Definition SC:**

> We say that a symmetrized set $\mathcal R$ of words over the
> alphabet $S^{\pm 1}$ satisfies the {\em condition $C(\e , \mu ,\rho
> )$} for the group $H$, if
> ($C_1$) All words from $\mathcal R$ are geodesic in $H$;
> ($C_2$) $|R|\ge \rho $ for any $R\in \mathcal R$;
> ($C_3$) The length of any $\e$-piece contained in any word $R\in \mathcal R$ is smaller than $\mu |R|$.

**Definition classQ:**

> We say that the presentation
> $\langle S\mid \mathcal R\rangle =\left\langle S\,\left|\,
> \bigcup\limits_{i=0}^\infty \mathcal R_i\right.\right\ra$
> of a group $G$ is a $\qq(\alpha,K)$-{\em presentation} if the
> following conditions hold for some sequences $\e =(\e_n)$, $\mu
> =(\mu _n)$, and $\rho =(\rho _n)$ of positive real numbers
> ($n=1,2\dots $).
> ($ \mathbf Q_0$) The group $G_0=\langle S\mid \mathcal R_0\rangle $
> is $\delta_0$-hyperbolic for some $\delta_0$.
> ($\mathbf Q_1$) For every $n\ge 1$, $\calr_{n}$ satisfies $C(\e_n,
> \mu _n, \rho _n)$ over $G_{n-1}=\left\langle S\, \left|\,\right.
> \bigcup\limits_{i=0}^{n-1} \mathcal R_i\right\rangle .$
> ($\mathbf Q_2$) $\mu_n=o(1)$, $\mu _n\le
> \alpha$, and $\mu_n\rho_n>K\e_n$ for any $n\ge 1$.
> ($\mathbf Q_3$) $\e_{n+1}>8\max\{|R|, R\in \calr_n\}=O(\rho_n)$.

**Lemma asc:**

> Let (\ref{qpres}) be a $\qq(.01, 10^6)$--presentation. Then the
> following conditions hold.
> (a) For every $n\ge 1$, Lemma \ref{gamma-cell} applies to
> $H=G_{n-1}$ and $H_1=G_{n}=\langle H\mid \mathcal R_{n}\rangle $.
> In particular, $G_n$ is $\delta _n$--hyperbolic, where $\delta
> _n\le 4\max\limits_{R\in \mathcal R_{n}}|R|$.
> (b) $\e _n=o(\rho _n)$.
> (c) $\rho _{n} =o(\rho _{n+1})$; in particular, $\rho _n\to
> \infty $ as $n\to \infty $ and $\delta _n=o(\rho _{n+1})$.
> (d) $\rho _n=o(r_S(G_{n}\to G_{n+1}))$, where $r_S$ is the
> injectivity radius.

**Naming:**

> From now {on} the condition $\qq=\qq(.01, 10^6)$ will be called the
> {\em graded small cancellation} condition.

**Mapping to the target.**
- (A1) is `C_2` inside `Q_1`, together with the `O(ρ_n)` clause of `Q_3`.
- (A2) is Lemma `asc`(c).
- (A3) is Lemma `asc`(d).
- (A4) is `Q_0` together with Lemma `asc`(a).

The proof of Lemma `asc` in the source also gives the sharper bound
"$|g|\ge (1-o(1))\rho_{n+1}$" for nontrivial `g ∈ Ker(G_n → G_{n+1})`. That bound is not used.
