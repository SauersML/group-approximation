# rev4.4 fixes from sk-perfect-b (credit/bibliography/abstract/prose), on rev4.3 md5 0648e5f8

Verdict: no false credit, no wrong statement.

## BIB-1, l.790–791 (Rădulescu volume title)
Before:
```latex
$R^\omega$}, Theta Ser. Adv. Math. \textbf{9}, Theta, Bucharest (2008),
173--185; preprint \arxiv{math/0004172} (2000).
```
After:
```latex
$R^\omega$}, in: Hot topics in operator theory, Theta Ser. Adv. Math.
\textbf{9}, Theta, Bucharest (2008), 173--185; preprint
\arxiv{math/0004172} (2000).
```

## BIB-2, l.732–734 (Margulis plural title + translation)
Before:
```latex
G.~A. Margulis, \emph{Explicit construction of a concentrator}
(Russian), Problemy Peredachi Informatsii \textbf{9} (1973), no.~4,
71--80.
```
After:
```latex
G.~A. Margulis, \emph{Explicit constructions of concentrators},
Problemy Peredachi Informatsii \textbf{9} (1973), no.~4, 71--80;
English transl., Problems Inform. Transmission \textbf{9} (1973), 325--332.
```

## ABSTRACT-1, l.29–42 (+3 lines)
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)} and a limit of finite simple groups
$\SL_{3N}(\F_2)$ whose Cayley graphs form expanders. So $G_X$ is locally
embeddable into finite groups, sofic and hyperlinear, which answers the
question of Brown and Ozawa whether an infinite simple Kazhdan group can
be hyperlinear, and Pestov's sofic version of it. A finitely generated group
is locally embeddable into finite groups if and only if it is a subgroup of
such a group, and it also has solvable word problem if and only if the host
can be chosen with solvable word problem. One such group contains every
recursively presented finitely generated group with this property, and the
groups $G_X$ realize every Turing degree as word problem degree, with
continuum many of them, none isomorphic to a subgroup of another.
\end{abstract}
```
Main's note: keep "that is a limit of finite simple groups" wording consistent with Cor 3; "such a group" = infinite f.g. simple Kazhdan group that is a limit of finite simple expanders. Verify each clause against the body at assembly.

## PROSE-1, l.71–73
Before:
```latex
The ring $\LC(X,\F_2)\rtimes_T\Z$ is finitely generated, so $G_X$ has
property~\textup{(T)}, introduced by Kazhdan~\cite{Kazhdan}, by the theorem
of Ershov and Jaikin-Zapirain~\cite{EJZ}. Periodic sequences approximating
```
After:
```latex
The ring $\LC(X,\F_2)\rtimes_T\Z$ is finitely generated, so by the theorem
of Ershov and Jaikin-Zapirain~\cite{EJZ} the group $G_X$ has Kazhdan's
property~\textup{(T)}~\cite{Kazhdan}. Periodic sequences approximating
```

## PROSE-2, l.105–107
Before:
```latex
The proof works for other actions. An action on a Cantor set is
topologically free if no nontrivial element fixes a nonempty open set,
and $e_{ij}(r)=I_n+rE_{ij}$ is an elementary matrix.
```
After:
```latex
The proof works for other actions. An action on a Cantor set is
topologically free if no nontrivial element fixes a nonempty open set.
We write $e_{ij}(r)=I_n+rE_{ij}$ for the elementary matrices.
```

## PROSE-3 (optional), l.96
`~\cite{Gromov87},~\cite[Theorem~1.5]{CoulonFournierFacio}` → `~\cite{Gromov87}, \cite[Theorem~1.5]{CoulonFournierFacio}`

## Still secondary (no change)
Ozawa p.527 (via Thom l.120, Pestov 8.5); KS Thm 1.2 (arXiv v1 numbering); Thompson80 content (BBMZ, Darbinyan–Steenbock); Odifreddi Ch. V; Rauzy Prop 26/Lemma 27 numbering source; Gromov87 no locator (CFF carries the claim).
