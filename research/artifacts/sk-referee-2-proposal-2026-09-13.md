# sk-referee-2: manuscript proposals (2026-09-13)

Line numbers refer to `manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99). The findings and checks are in `research/artifacts/sk-referee-2-report-2026-09-13.md`. None of these proposals changes a statement; they state conventions and choices the reader otherwise has to reconstruct.

Summary of the length changes, in source lines of the text:

| Proposal | Location | Change |
|---|---|---|
| P1 | l.123-129 | +1 |
| P2 | l.131-144 | 0 |
| P3 | l.146-152 | +1 |
| P4 | l.119 | 0 in the text, +5 in the bibliography |
| P5 | l.240-242 | +2 |
| P6 | l.251-252 | +2 |
| P7 | l.257-261 | 0 |

## P1 (U1): the repeated segment (l.123-129)
Current:
```latex
For each $k$, there is a periodic sequence $y=w^\infty$ with exactly
the same words of length $2k+1$ as $X$. Indeed, minimality implies
uniform recurrence. In a point of $X$, choose two occurrences of the
same word of length $2k$, separated by a segment $w$ long enough to
contain every word of length $2k+1$. Repeating this segment introduces
no new word of that length at the join. Its length $N$ can be chosen
arbitrarily large.
```
Replacement:
```latex
For each $k$, there is a periodic sequence $y$ with the same words of
length $2k+1$ as $X$, and its period can be arbitrarily large. Indeed,
minimality implies uniform recurrence, so a point $x\in X$ has positions
$p<q$, with $q-p$ as large as we like, such that
$x_p\cdots x_{p+2k-1}=x_q\cdots x_{q+2k-1}$ and $w=x_p\cdots x_{q-1}$
contains every word of length $2k+1$. Put $y=\cdots www\cdots$, with
period $N=q-p$. Each window of length $2k+1$ of $y$ is a window of
$x_p\cdots x_{q+2k-1}$.
```
- Trade-off: +1 line. The current wording also admits w as the gap between the occurrences, and under that reading the claim is false. The replacement fixes the choice and gives the one-line reason for the join.
- Status: checked (report §1). No node.

## P2 (U2): the diagonal model (l.131-144)
Current:
```latex
Let $P\delta_n=\delta_{n+1}$ on $\F_2^{\Z/N\Z}$. If $f$ depends on a
window $[-\rho,\rho]$, evaluate its local table along $y$ to obtain a
diagonal matrix $D_y(f)$. Send
\[
  \sum_j f_ju^j\ \longmapsto\ \sum_j D_y(f_j)P^j.
\]
For any fixed finite list of sums and products in $R$, choose $k$
larger than all windows involved, including those shifted in the
products. The relation
$P^iD_y(f)P^{-i}=D_y(f\circ T^{-i})$ then preserves every listed
operation. Nonzero coefficients remain nonzero, since every allowed
window occurs in $y$. Taking $N$ larger than twice the largest absolute
exponent makes the corresponding cyclic diagonals distinct; hence
nonzero differences also remain nonzero.
```
Replacement:
```latex
Let $P\delta_n=\delta_{n+1}$ on $\F_2^{\Z/N\Z}$. If
$f(x)=\varphi(x_{-\rho}\cdots x_{\rho})$ with $\rho\le k$, put
$D_y(f)\delta_n=\varphi(y_{n-\rho}\cdots y_{n+\rho})\delta_n$, and send
\[
  \sum_j f_ju^j\ \longmapsto\ \sum_j D_y(f_j)P^j.
\]
For a fixed finite list of sums and products in $R$, choose $k$ at
least the window radius of every coefficient involved, including the
coefficients $f\circ T^{-i}$ created by the products. Then
$P^iD_y(f)P^{-i}=D_y(f\circ T^{-i})$ preserves every listed operation.
Nonzero coefficients remain nonzero, since every word of $X$ of length
$2k+1$ occurs in $y$. If $N$ exceeds twice the largest absolute exponent,
distinct exponents give disjoint cyclic diagonals, so nonzero
differences also remain nonzero.
```
- Trade-off: same length. The relation $P^iD_y(f)P^{-i}=D_y(f\circ T^{-i})$ holds for one indexing only, and the current text does not say which. The replacement also removes the undefined "allowed window" and replaces "hence" with "so".
- Status: checked (report §2). No node.

## P3 (U3, C1): group models, sofic and hyperlinear (l.146-152)
Current:
```latex
For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```
Replacement:
```latex
For finite $F\subseteq G$, list the entries of the elements of
$F\cup F^{-1}$ and of their differences, together with the sums and
products in the matrix products $gh$ for $g,h\in F\cup F^{-1}$. The
entrywise model $\Phi$ is injective on $F$, satisfies
$\Phi(gh)=\Phi(g)\Phi(h)$ whenever $g,h,gh\in F$, and
$\Phi(g)\Phi(g^{-1})=I_{3N}$, so $\Phi(F)\subseteq\GL_{3N}(\F_2)$.
Thus $G$ is LEF. LEF groups are sofic, and sofic groups are
hyperlinear~\cite[Example~4.5 and Theorem~3.3]{Pestov}.
```
- Trade-off: +1 line. The images are invertible because $gg^{-1}$ is among the listed products, which the current text leaves implicit. The last sentence cites two exact statements, where the current text presents the hyperlinear step as immediate; Pestov notes that the comparison of distances there is not Lipschitz.
- Status: checked against arXiv:0804.3968v8.
  - Example 4.5 (p. 12) reads "Every initially subamenable group is sofic". The sentence just before it reads "So is every LEF group G in the sense of Vershik and Gordon [75]" (initially subamenable).
  - Theorem 3.3 (p. 7) reads "(Elek and Szabó [26]). Every sofic group is hyperlinear."
  - The journal numbering (BSL 14 (2008)) is not checked; that belongs to sk-citations.

## P4 (C2): credit for LEF (l.119)
Current:
```latex
A group is LEF if every finite subset embeds injectively into a finite
```
Replacement:
```latex
A group is LEF~\cite{VershikGordon} if every finite subset embeds injectively into a finite
```
Add to the bibliography, after `\bibitem{Thom}` (alphabetical):
```latex
\bibitem{VershikGordon}
A.~M. Vershik and E.~I. Gordon,
\emph{Groups that are locally embeddable in the class of finite groups},
Algebra i Analiz \textbf{9} (1997), no.~1, 71--97; English transl.,
St. Petersburg Math. J. \textbf{9} (1998), no.~1, 49--67.
```
- Trade-off: +5 bibliography lines. The note's title theorem uses LEF, and this is the source of the notion (Pestov's guide attributes it the same way).
- Status: the bibliographic data is copied from main's `formalization.yaml` (entry "Groups that are locally embeddable in the class of finite groups", id mathnet.ru/eng/aa751) and not rechecked by this lane. sk-citations should confirm the pages.

## P5 (U4): the upper bound for the word problem (l.240-242)
Current:
```latex
An oracle for $L(X)$ decides whether a matrix word equals $I_3$, by
checking the coefficient tables of its difference from $I_3$ on the
allowed windows. Conversely, for a word $v=v_0\cdots v_{n-1}$, the cylinder
```
Replacement:
```latex
A matrix word can be multiplied out in $\LC(A^{\Z},\F_2)\rtimes\Z$,
which maps onto $R$, and it equals $I_3$ if and only if the coefficient
tables of its difference from $I_3$ vanish on the words of $L(X)$. So an
oracle for $L(X)$ decides the word problem. Conversely, for a word
$v=v_0\cdots v_{n-1}$, the cylinder
```
- Trade-off: +2 lines. The replacement names where the computation happens (the full-shift algebra, whose restriction map onto $R$ is a ring homomorphism) and replaces the undefined "allowed windows".
- Status: checked (report §5). No node. The reduction is in fact truth-table.

## P6 (U5): define the Sturmian subshift (l.251-252)
Current:
```latex
Now use the infinite minimal Sturmian subshift of an irrational slope
$\alpha\in(0,1)$~\cite{MorseHedlund}. Its language is computable from
```
Replacement:
```latex
Now use the Sturmian subshift $X_\alpha$ of an irrational
$\alpha\in(0,1)$, the closure of the codings
$t\mapsto1_{[1-\alpha,1)}(\theta+t\alpha\bmod1)$; it is infinite and
minimal~\cite{MorseHedlund}. Its language is computable from
```
l.253-256 are unchanged. With this convention the letter at $t$ is $1$ if and only if $\theta\in[-(t+1)\alpha,-t\alpha)$. So the words of length $n$ are determined by the cyclic order of the points $-j\alpha$, $0\le j\le n$, as l.253-254 say, and a word of length $n$ has $\lfloor\theta+n\alpha\rfloor$ ones, so l.255-256 hold.
- Trade-off: +2 lines. The endpoint set at l.254 presupposes this coding, and the note never defines $X_\alpha$. Both computability claims become one-line checks.
- Fuller variant (+4 lines), which also writes those two checks into the text:
```latex
Now use the Sturmian subshift $X_\alpha\subseteq\{0,1\}^{\Z}$ of an
irrational $\alpha\in(0,1)$~\cite{MorseHedlund}, the closure of the
codings $x_t=1_{[1-\alpha,1)}(\theta+t\alpha\bmod1)$, $\theta\in[0,1)$;
it is infinite and minimal. Such a coding has $x_t=1$ if and only if
$\theta$ lies in the arc $[-(t+1)\alpha,-t\alpha)$, so the words of
length $n$ are determined by the cyclic order of the points
$-j\alpha\bmod1$, $0\le j\le n$, and $L(X_\alpha)$ is computable from
$\alpha$. A word of length $n$ has $\lfloor\theta+n\alpha\rfloor$ ones,
so the least number of ones is $\lfloor n\alpha\rfloor$ and $L(X_\alpha)$
computes $\alpha$.
```
(This replaces l.251-256.) My reader-merits verdict is the short version. The two checks are routine once the coding is stated.
- Status: checked (report §5). No node.

## P7 (S1): irrational representatives (l.257-261)
Current:
```latex
Every Turing degree has an irrational representative: use $\sqrt2-1$
for the computable degree, and interleave the characteristic sequence
of a noncomputable set with 1's in a binary expansion for any other
degree. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
```
Replacement:
```latex
Every Turing degree has an irrational representative in $(0,1)$: use
$\sqrt2-1$ for the computable degree and $\sum_{i\in S}2^{-i-1}$ for a
noncomputable set $S$, whose binary expansion is not eventually
periodic. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
```
- Trade-off: same length, and simpler. The binary expansion of a noncomputable set is already not eventually periodic, so the real is irrational, not dyadic, and has the degree of the set; the interleaving device is unexplained and unnecessary.
- Status: checked (report §5). No node.

## Not proposed
- tt- and m-refinements of the degree statement: true (report §5), but not stronger in a way this note's reader needs.
- l.180, $2w+3$ versus $2w+2$: outside my scope; left for sk-referee-1.
