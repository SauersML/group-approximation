# Verbatim sources for the lamplighter-closure obstruction (2026-09-17)

Lane `e-f-transplant` (stability-approximation transplant toward
`zaremsky-2-01-thompson-f-amenable`). The quotes below were copied from the arXiv TeX
sources, downloaded on 2026-09-17:

- **[FFR]** F. Fournier-Facio and B. Rangarajan, *Ulam stability of lamplighters and Thompson
  groups*, arXiv:2301.03970 (source `Ulam_F.tex`, dated July 2023).
- **[M]** N. Monod, *Lamplighters and the bounded cohomology of Thompson's group*,
  arXiv:2112.13741v1 (source `bacyclic8.tex`).

TeX macros were expanded by hand: `\Uf` is the family `U_f`, `\Ha^n` and `\HH^n_a` are
`H^n_a`, `\hGamma` is `*Gamma`, and `\hb^n` is `H^n_b`. The theorem numbers are the labels
used in the source.

## [FFR] setting

> Let $\Uf := \{ (U(k), \| \cdot \|) \}$ be a family of finite-dimensional unitary groups equipped
> with bi-invariant submultiplicative norms $\| \cdot \|$ (we allow $U(k)$ to appear multiple times
> with different norms). For instance $\| \cdot \|$ could be the operator norm - the most classical
> case - or more generally a Schatten $p$-norm.

> The group $\Gamma$ is \emph{uniformly $\Uf$-stable} if every uniform asymptotic homomorphism is
> uniformly asymptotically close to a sequence of homomorphisms.

Kazhdan's theorem, as FFR quote it:

> In this contest, Kazhdan proved stability of amenable groups \cite{kazhdan}, while Burger, Ozawa
> and Thom proved stability of certain special linear groups over $S$-integers, and instability of
> groups admitting non-trivial quasimorphisms \cite{BOT}.

> This can be seen as a relative version of the celebrated result of Kazhdan, stating that amenable
> groups are uniformly $\Uf$-stable \cite{kazhdan}.

## [FFR] the three heredity statements

Theorem `intro:thm:F`:

> Thompson's groups $F, F', T$ and $V$ are uniformly $\Uf$-stable, with a linear estimate.

Theorem `intro:thm:lamplighters` (the lamplighter axiom (L)):

> Let $\Gamma, \Lambda$ be two countable groups, where $\Lambda$ is infinite and amenable. Then
> $\Gamma \wr \Lambda$ is uniformly $\Uf$-stable, with a linear estimate.

Proposition `intro:prop:coamenable` (the coamenable axiom (C)):

> Let $\Lambda \leq \Gamma$ be coamenable. If $\Lambda$ is uniformly $\Uf$-stable with a linear
> estimate, then so is $\Gamma$.

Proposition `intro:prop:mapping` (the quotient axiom (Q)):

> Let $N \leq \Gamma$ be an amenable normal subgroup. If $\Gamma$ is uniformly $\Uf$-stable with a
> linear estimate, then so is $\Gamma / N$.

Theorem `intro:thm:lamplighters:ac`:

> Let $\Gamma, \Lambda$ be two countable groups, where $\Lambda$ is infinite and amenable. Then
> $\Ha^n(\Gamma \wr \Lambda, \V) = 0$ for all $n \geq 1$ and all finitary dual asymptotic Banach
> $\hGamma$-modules $\V$.

## [FFR] the self-similar mechanism used for F'

Lemma `lem:metabelian:kernel`:

> Let $\Gamma$ be a group, and suppose that there exists $g \in \Gamma$ and $\Gamma_0 \leq \Gamma$
> such that $\{g^i \Gamma_0 g^{-i} : i \in \mathbb{Z} \}$ pairwise commute. Then there exists an
> epimorphism $\Gamma_0 \wr \mathbb{Z} \to \langle \Gamma_0, g \rangle$ with amenable (in fact,
> metabelian) kernel.

Lemma `lem:coamenable:commuting`, citing [M, Proposition 10]:

> Suppose that $\Gamma_0 \leq \Gamma$ is such that every finite subset of $\Gamma$ is contained in
> some $\Gamma$-conjugate of $\Gamma_0$. Then $\Gamma_0$ is coamenable in $\Gamma$.

Lemma `lem:coamenable:constructions`:

> Let $K \leq H \leq \Gamma$.
> 1. If $K$ is coamenable in $\Gamma$, then $H$ is coamenable in $\Gamma$;
> 2. If $K$ is coamenable in $H$ and $H$ is coamenable in $\Gamma$, then $K$ is coamenable in
>    $\Gamma$.

Proof of Corollary `cor:bsupp`, for a proximal, boundedly supported group of
orientation-preserving homeomorphisms of the line:

> Let $\Gamma_0$ be the subgroup of elements whose support is contained in $[0, 1]$. Let
> $g \in \Gamma$ be such that $g(0) > 1$: such an element exists because the action of $\Gamma$ is
> proximal. Then it follows by induction, and the fact that $\Gamma$ is orientation-preserving,
> that the intervals $\{ g^i[0, 1] : i \in \mathbb{Z} \}$ are pairwise disjoint. Therefore the
> conjugates $g^i \Gamma_0 g^{-i}$ pairwise commute.
>
> Since $\Gamma$ is boundedly supported, for every finite subset $A \subset \Gamma$ there exists $n$
> such that the support of each element of $A$ is contained in $[-n, n]$. By proximality, there
> exists $h \in \Gamma$ such that $h(0) < -n$ and $h(1) > n$. Then $h \Gamma_0 h^{-1}$ is the
> subgroup of elements whose support is contained in $[-n, n]$, in particular it contains $A$.

The facts about F:

> The derived subgroup $F'$ coincides with the subgroup of boundedly supported elements.

> We identify $(0, 1)$ with the real line. The group $F'$ is boundedly supported, and it is
> proximal, since it acts transitively on ordered pairs of a dense set.

> Since the quotient $F/F'$ is abelian, thus amenable, we see that $F'$ is coamenable in $F$

> It is well known that $F'$ and $F$ contain a coamenable lamplighter $F \wr \mathbb{Z}$.

Remark after Corollary `cor:F` (uniform data of F factor through Z^2):

> Therefore uniform $\Uf$-stability of $F'$ implies that every uniform asymptotic homomorphism
> $F' \to \Uf$ is uniformly asymptotically close to the trivial one. It follows that every uniform
> asymptotic homomorphism $F \to \Uf$ is uniformly asymptotically close to one that factors through
> $\mathbb{Z}^2$.

## [FFR] approximability, and the uniform/pointwise split

Corollary `cor:F:uniapprox`:

> As usual, let $\Uf$ be the family of unitary groups equipped with submultiplicative norms. Then
> Thompson's groups $F, F', T$ and $V$ are not uniformly $\Uf$-approximable. The same holds for
> $\Gamma \wr \Lambda$, whenever $\Lambda$ is infinite and amenable, and $\Gamma$ is non-abelian.

Corollary `cor:F:pwapprox`:

> Let $\mathcal{G}$ be the family of symmetric groups with the normalized Hamming distance, the
> family of unitary groups with the Hilbert--Schmidt norm, or the family of unitary groups with the
> operatorn norm. If Thompson's group $F$ is pointwise $\mathcal{G}$-stable, then it is not
> pointwise $\mathcal{G}$-approximable, and in particular it is non-amenable.

The strong (infinite-dimensional) version is not covered, from Remark `rem:sharp:lamplighters`:

> It is shown in \cite{BOT} that a subgroup of a strongly Ulam stable group is Ulam stable.
> Therefore it is clear that Theorem \ref{intro:thm:lamplighters} does not hold for strong Ulam
> stability. Even restricting to separable Hilbert spaces does not help: it follows from the
> construction in \cite{BOT} that if a \emph{countable} group contains a free subgroup, then
> separable Hilbert spaces already witness the failure of strong Ulam stability.

## [M] bounded cohomology

Theorem `thm:F:sep`:

> The vanishing $\hb^n(F,E)=0$ holds for all $n>0$ and all separable dual Banach $F$-modules $E$.

What immediately follows it:

> This is the first known example of acyclicity for such general coefficients --- except of course
> amenable groups.
>
> However we caution the reader that this statement does not answer the amenability question.
> Indeed, our proof also works for many groups that are similar to $F$ but known to be
> non-amenable. For instance, the proof holds unchanged for all piecewise-projective groups
> introduced in~\cite{Monod_PNAS}.

Theorem `thm:sep`:

> Let $G$ be any group and consider the wreath product
> $W = G \wr \ZZ = \Big( \bigoplus_{\ZZ} G \Big) \rtimes \ZZ.$
> Then $\hb^n(W,E)$ vanishes for all $n>0$ and all separable dual Banach $W$-modules $E$.
