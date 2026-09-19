# Kun–Thom arXiv:2608.06222v1, Section 4: where the ambient group enters (verbatim source excerpts)

Provenance. These are excerpts from the LaTeX e-print source of arXiv:2608.06222v1
(G. Kun and A. Thom, *Nonsofic wreath products of residually finite groups*). The file is
`secondpaper.tex`, 67198 bytes, with timestamp 2026-08-06 16:11. It was re-read line by line
on 2026-09-19. Line numbers refer to that file. The statements of Theorem 4.1, Proposition 3.1
and the infranormality definition agree word for word with the HTML transcription in
`research/artifacts/kun-thom-2608-06222-verified.md`. The trust surface is the same as for
that record: an unrefereed preprint, not kernel-checked.

The excerpts are copied exactly, apart from the `>` quoting. They cover every sentence of
Section 4 (lines 693–1362) and of the proof of Proposition 3.1 (lines 476–618) that mentions
- property (T);
- the constant `h_G`;
- the ambient partition `\cA_n` / `\mathcal A_n`;
- the ambient generator graph; or
- a citation.

## A. The statement, and the only mention of (T) in Section 4

Lines 709–714:

```
\begin{theorem}\label{thm:permutation-centralizer}
Let $\Gamma$ be an infranormal subgroup of $G$, and suppose that both
$\Gamma$ and $G$ have Kazhdan's property~$(T)$.  If
$\sigma:G\to\cS_{\cU}$ is a sofic representation, then
$C_{\cS_{\cU}}(\sigma(\Gamma))$ is normalized by $\sigma(G)$.
\end{theorem}
```

Mechanical check (grep over Section 4, lines 692–1363):
- the word `Kazhdan` occurs only at line 699, which is about Γ (excerpt B), and line 711;
- the string `Theorem~1]{Kun}` occurs only at line 721, where it is applied to `σ|_Γ`
  (excerpt C);
- `h_G` occurs only at line 1033;
- `\mathcal A_n` or the word `ambient` occurs only at lines 857, 1031, 1033, 1039, 1046,
  1066, 1067, 1070, 1072 and 1084;
- the main proof (lines 1106–1362) reaches the ambient partition only through the two
  applications of Lemma 4.4 at lines 1189–1191.

## B. Section opening: the cluster groupoid is a Γ-object (lines 695–702)

```
The purpose of this section is to strengthen
Proposition~\ref{prop:normalization}.  We show that the conclusion holds not
only for the diagonal fixed-point algebra, but also for the permutation
centralizer.  The additional input is the finite cluster groupoid associated
with a sofic approximation of a Kazhdan group
\cite{AlekseevThomCentralizers}.
```

## C. Setup: Kun's theorem is applied to Γ only (lines 716–730)

```
We first recall the part of the cluster construction that will be used.  Let
$S=S^{-1}$ be a finite generating set of $\Gamma$, let $F=F_S$ be the free
group on $S$, and choose homomorphisms
$\alpha_n:F\to\Sym(Y_n)$ representing $\sigma|_\Gamma$.
By the expander decomposition theorem
\cite[Theorem~1]{Kun}, after changing
$o_{\cU}(|Y_n|)$ generator edges, we obtain the component partition
$Y_n=\bigsqcup_{i\in I_n^0}Q_{n,i}$,
where the $Q_{n,i}$ are $F$-orbits and their labelled graphs have Cheeger
constant at least a fixed number $h_\Gamma>0$.
```

## D. Lemma 4.2 is built from σ|_Γ (lines 807–811)

```
This is the construction of
\cite[Proposition~3.3, Lemma~3.4, Definition~4.1 and
Proposition~4.5]{AlekseevThomCentralizers}, with the
scale chosen diagonally.
```

## E. Convention on the ambient decomposition (lines 854–861)

```
From now on, $I_n$ and $Y_n^{\mathrm{good}}$ have the meaning supplied by
Lemma~\ref{lem:joint-cluster-scales}.  We keep
$Y_n\setminus Y_n^{\mathrm{good}}$ inside the original $Y_n$ as a global
exceptional set.  In particular, the ambient $G$-expander decomposition is
always taken on the original set $Y_n$.
```

## F. Lemma 4.3 imports the matching of Proposition 3.1 (lines 898–902)

```
\begin{proof}
Before choosing the cluster scale, apply the quantitative component matching
used in the proof of Proposition~\ref{prop:normalization} to the full
partitions $\{u_nQ_{n,i}:i\in I_n^0\}$ and
$\{Q_{n,j}:j\in I_n^0\}$.
```

## G. Lemma 4.4, the only place `\mathcal A_n` is introduced in Section 4

Lines 1031–1033:

```
Let $\mathcal A_n$ be the component partition of the edited
$G$-generator graph.  Its components have Cheeger constant bounded below by
$h_G>0$.  We keep this ambient decomposition on the original set $Y_n$.
```

Lines 1044–1047. This is a crossing count, property (AP1) of the proof node:

```
provided that $x$ belongs to a retained matched component,
$u_{\ell,n}x$ belongs to its matched target, and both vertices lie in the
same ambient component.  All failures of these conditions form a set
$E_{\ell,n}$ with $|E_{\ell,n}|=o_{\cU}(|Y_n|)$.
```

Lines 1064–1074. This is a summed median inequality, property (AP2) of the proof node:

```
The variation along the $\Gamma$-edges is also
$o_{\cU}(|Y_n|)$ because $H_n$ is constant on the $\Gamma$-components,
up to the negligible restricted and ambient edits.  It follows that the
total variation of $H_n$ on the edited ambient $G$-graph is
$o_{\cU}(|Y_n|)$.

Lemma~\ref{lem:median}, applied on each ambient component and summed, gives
\[
        \sum_{A\in\mathcal A_n}
        \sum_{x\in A}|H_n(x)-1/2|
        =o_{\cU}(|Y_n|).
\]
```

Line 1084. The witness condition, again (AP1):

```
and $x,u_{\ell,n}x$ lie in the same member of $\mathcal A_n$.  If a
```

## H. Main proof: the generating family and the two calls to Lemma 4.4

Lines 1106–1109:

```
\begin{proof}[Proof of Theorem~\ref{thm:permutation-centralizer}]
Choose $t_1,\ldots,t_m\in P_\Gamma$, including any prescribed element of
$P_\Gamma$, such that $G=\langle\Gamma,t_1,\ldots,t_m\rangle$.
Apply Lemmas~\ref{lem:joint-cluster-scales} and
```

Line 1191:

```
Apply Lemma~\ref{lem:one-sided-median} first to $o_n$ and then to $k_n$.
```

Lines 1342–1348 and 1357–1361 (the reverse inclusion and the conclusion, which are algebraic):

```
The reverse inclusion follows from the compression relation.  Indeed, for
$c\in C_{\cS_{\cU}}(\sigma(\Gamma))$ and $\gamma\in\Gamma$,
\[
 [\sigma(t_\ell)^{-1}c\sigma(t_\ell),\sigma(\gamma)]
 =
 \sigma(t_\ell)^{-1}
 [c,\sigma(t_\ell\gamma t_\ell^{-1})]
[...]
Conjugating this inclusion by $\sigma(t_\ell)$ and combining it with
\eqref{eq:forward-centralizer-inclusion} gives equality.  The
centralizer is fixed pointwise under conjugation by $\sigma(\Gamma)$, and
$G=\langle\Gamma,t_1,\ldots,t_m\rangle$.  Hence it is normalized by
$\sigma(G)$.
```

## I. Proposition 3.1: statement and every use of `\cA_n`

Lines 464–474. The statement's ambient hypothesis is a decomposition, not (T):

```
\begin{proposition}\label{prop:normalization}
Let $\Gamma$ be an infranormal subgroup of $G$, and assume that both
$\Gamma$ and $G$ are finitely generated.  Let
$\sigma:G\to\cS_{\cU}$ be a sofic
representation.  Assume that the generator graphs of both
$\sigma|_\Gamma$ and $\sigma$ admit, after
$o_{\cU}(|Y_n|)$ edge changes, decompositions into components with
uniform positive Cheeger constants.  Then
$\sigma(g)D_{\cU}^{\sigma(\Gamma)}\sigma(g)^{-1}
=D_{\cU}^{\sigma(\Gamma)}$ for every $g\in G$.
\end{proposition}
```

Lines 477–486. The ambient generating set:

```
Since $G$ is finitely
generated and $P_\Gamma$ generates $G$, there are
$t_1,\ldots,t_m\in P_\Gamma$ such that
$G=\langle\Gamma,t_1,\ldots,t_m\rangle$.  Fix a finite symmetric
generating set $S_\Gamma$ of $\Gamma$ and use
$S_G=S_\Gamma\cup\{t_1^{\pm1},\ldots,t_m^{\pm1}\}$ for $G$.  Let
$\cQ_n$ be a component partition into edited $\Gamma$-expanders with
Cheeger constant at least $h_\Gamma>0$, and let $\cA_n$ be a component
partition into edited ambient $G$-expanders with Cheeger constant at
least $h_G>0$.
```

Lines 533–536 and 541–542. This is (AP1) for the `S_Γ`-edges and for the `t_i`-edges:

```
component.  Outside the union of the $o_{\cU}(|Y_n|)$ restricted edge
edits and the $o_{\cU}(|Y_n|)$ ambient edge edits, an original
$S_\Gamma$-edge has both endpoints in the same $\cQ_n$-cell and in the
same $\cA_n$-cell.
[...]
All but $o_{\cU}(|Y_n|)$ of the $t_i$-edges have both endpoints in the
same ambient component.
```

Lines 559–566. This is (AP2):

```
Repeating the argument for each $t_i$, and accounting for the
negligible ambient edge edit, shows that the total variation of $f_n$
on the edited ambient $G$-graph is $o_{\cU}(|Y_n|)$.

Apply Lemma~\ref{lem:median} on every $A\in\cA_n$ and sum over $A$.
We obtain
\[
 \sum_{x\in Y_n}\left|f_n(x)-\frac12\right|
 =o_{\cU}(|Y_n|).
\]
```

Lines 571–572 and 581–583. After this, the cells are used only through the concentration and
through (AP1):

```
$o_{\cU}(|Y_n|)$ vertices.  If $x,y\in A\setminus E_n$ for an
ambient cell $A$, then
[...]
Let
$H_{i,n}=\{x\in Y_n:A_n(x)\neq A_n(\tau_nx)\}$; this set has
$o_{\cU}(|Y_n|)$ vertices.
```

## J. Lemma 2.3 (the median inequality), lines 409–416

```
\begin{lemma}\label{lem:median}
Let $\mathcal G$ be a finite graph with $h(\mathcal G)\geq h>0$.
If $f:V(\mathcal G)\to\mathbb R$ and $m$ is a median of $f$, then
\[
 h\sum_{x\in V(\mathcal G)}|f(x)-m|
 \leq
 \sum_{\{x,y\}\in E(\mathcal G)}|f(x)-f(y)|.
\]
\end{lemma}
```
