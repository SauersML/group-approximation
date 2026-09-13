---
rg: 2
id: cepss-nonhausdorff-steinberg-simplicity-citation
kind: route
title: Clark–Exel–Pardo–Sims–Starling, quoted verbatim from the arXiv TeX source
target: cepss-nonhausdorff-steinberg-simplicity
requires: []
---

Imported from L. O. Clark, R. Exel, E. Pardo, A. Sims, C. Starling, *Simplicity of algebras associated to
non-Hausdorff groupoids*, arXiv:1806.04362. Quoted verbatim from the arXiv TeX source
`CEPSS_revision_Mar07_2019.tex` (e-print fetched on MSI, 2026-09-13; line numbers of that file).

**(S) lines 808–819.**

> \begin{thm} \label{thm:simple} Let $\G$ be a second-countable, ample groupoid such that $\go$ is Hausdorff.
> Then $A_\KK(\G)$ is simple if and only if the following three conditions are satisfied: \begin{enumerate}
> \item\label{it1:thm} $\G$ is minimal, \item\label{it2:thm} $\G$ is effective, and \item\label{it3:thm} for every
> nonzero $f\in A_\KK(\G)$, $\supp(f)$ has nonempty interior. \end{enumerate}

**Singular ideal, lines 612–614.**

> \begin{prop}\label{prop:singularideal} Let $\G$ be an ample groupoid with Hausdorff unit space. Then the set
> $\s_\KK(\G)$ of singular elements is an ideal of $A_\KK(\G)$.

**(B) line 2159, and before line 2280.**

> We use the notation $\ggx:= \gt(\sgx)$. Then $\ggx$ is ample and minimal, and since the action of $G$ on $X^*$ is
> faithful, then $\ggx$ is effective, see \cite[Section 17]{EP17}.

> none of the prefixes of the words in question are strongly fixed. Hence $\ggx$ is not Hausdorff.

**(G0) lines 2281–2289.**

> \begin{thm}\label{thm:grigsimple} Let $G$ be the Grigorchuk group, let $(G,X)$ be its self-similar action, and let
> $\ggx$ be the associated groupoid. Then \begin{enumerate} \item\label{it:grigthm1} For any field $\KK$ of
> characteristic zero, $A_\KK(\ggx)$ is simple, and \item\label{it:grigthm2} $\ogx$ is simple. \end{enumerate}
> \end{thm} Interestingly, simplicity can fail when $\KK$ has nonzero characteristic, see
> Corollary~\ref{cor:grigZ2notsimple}.

**(P) Where characteristic enters.**
- Lines 2395–2401, 2416–2424:

  > \begin{lemma}\label{lem:LCzero} Let $m\in \N$, let $\KK$ be a field of characteristic zero, and let
  > \begin{equation}\label{eq:singularLC} f = \sum_{g\in \{e, b, c, d\}}c_g 1_{U_{g, m}} \end{equation} for some
  > $c_g\in \KK$. Then supp$(f)$ has empty interior if and only if $f$ is identically zero.

  > This leads to the following six equations \begin{align} c_e + c_b = 0 && c_c + c_d = 0\nonumber\\ c_e + c_c = 0 &&
  > c_b + c_d = 0\label{eq:homlinearequations}\\ c_e + c_d = 0 && c_c + c_b = 0\nonumber \end{align} and since $\KK$
  > has characteristic zero, this has the unique solution $c_e = c_b = c_c = c_d = 0$.

- Lines 2507–2512 and 2531:

  > \begin{lemma}\label{lem:zeinterior} Let $\KK$ be a field of characteristic zero, and let $f\in A_\KK(\ggx)$. If
  > $f(z_e)\neq 0$, then supp$(f)$ has nonempty interior.

  > By Lemma~\ref{lem:basisISG} and \cite[Lemma~4.14]{St}, we may assume each element of $F$ is of the form
  > $\Theta((\alpha, g,\beta), C(\beta\eta))$.

  > Hence by Lemma~\ref{lem:LCzero}, the support of this function has nonempty interior.

- Lines 2535–2538 and the proof's closing lines:

  > \begin{lemma}\label{lem:grigsingular} Suppose that $\KK$ is a field of characteristic zero, let $f\in
  > A_\KK(\ggx)$, and suppose $f\in \s_\KK(\ggx)$ (that is, supp$(f)$ has empty interior). Then $f$ is identically
  > zero.

  > The singular elements form an ideal by Proposition~\ref{prop:singularideal}, and so $1_B * f * 1_C$ is singular.
  > But by Lemma~\ref{lem:zeinterior}, singular elements must be zero at $z_e$, a contradiction.

  > \begin{proof}[Proof of Theorem~\ref{thm:grigsimple}\eqref{it:grigthm1}] This follows from
  > Theorem~\ref{thm:simple} and Lemma~\ref{lem:grigsingular}.

**(G2) lines 2431–2440.**

> \begin{cor}\label{cor:grigZ2notsimple} Let $G$ be the Grigorchuk group, let $(G,X)$ be its self-similar action, and
> let $\ggx$ be the associated groupoid. Then $\s_{\Z_2}(\ggx)$ is nonzero, and hence the Steinberg algebra
> $A_{\Z_{2}}(\ggx)$ is not simple. \end{cor} \begin{proof} Consider $f:= \sum_{g\in \{e,b,c,d\}} 1_{U_{g,1}}$, that
> is, take $c_g = 1\in\Z_2$ for all $g\in \{e,b,c,d\}$ in \eqref{eq:singularLC}. Then the equations
> \eqref{eq:homlinearequations} are satisfied, and so supp$(f)$ has empty interior.

CEPSS add that this corollary "is also proved in \cite[Example~4.5]{Nek16}", where Nek16 is V. Nekrashevych, *Growth of
étale groupoids and simple algebras*, Internat. J. Algebra Comput. 26(2) (2016), 375–397.
