# sk-exposition proposal, part 3: sentence-level pairs for l.154–262, and the line-count table (2026-09-13)

**Line numbers:** from `$SK/manuscript-disk-1646.tex`. The "after" text applies the renames from part 1, E1: $N\to K$, $k\to g_1$, $e\to e_V$.

## P11. l.154–155: heading and tower hypothesis (0 lines)
Before:
```latex
\subsection*{A finite tower detects every normal subgroup}
Suppose the levels $T^aU$ are disjoint for all indices needed below.
```
After:
```latex
\subsection*{Simplicity}
Let $U$ be clopen, with the sets $T^aU$, $|a|\le m$, pairwise disjoint.
```
Trade-off: "detects" is a metaphor. "for all indices needed below" makes the reader search forward for the hypothesis.

## P12. l.166–173: the unit and absorption (0 lines)
Before:
```latex
with unit $e_{\bigcup_{|a|\le m}T^aU}$. If $r,r'$ involve only powers
$u^j$ with $|j|\le w$, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U),
\end{equation}
provided the larger tower is disjoint. To see this, multiplying
$E_{ab}(W)$ on the left by $fu^i$ and on the right by $f'u^j$ changes
its indices to $(a+i,b-j)$ and restricts its clopen coefficient.
```
After:
```latex
with unit $e_V$, $V=\bigcup_{|a|\le m}T^aU$. If $r,r'$ involve only
powers $u^j$ with $|j|\le w$, and the sets $T^aU$, $|a|\le m+w$, are
pairwise disjoint, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U).
\end{equation}
Indeed, $fu^iE_{ab}(W)f'u^j=E_{a+i,\,b-j}(W')$ for some clopen
$W'\subseteq W$.
```
Trade-off:
- The hypothesis now comes before the conclusion.
- One formula replaces the dangling "To see this, multiplying ... changes its indices".
- The unit gets a name, used in P14.

Check:
- $fu^ie_{T^aW}u^{a-b}=e_{T^{a+i}W_1}u^{a+i-b}$ with $W_1\subseteq W$.
- Then $e_{T^{a'}W_1}u^{a'-b}f'u^j=e_{T^{a'}W'}u^{a'-(b-j)}$ with $W'\subseteq W_1$.

## P13. l.185–187: the subring argument (+1 line; precision)
Before:
```latex
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
a subring containing all ring generators, so $g\in Z(G)=\{1\}$.
```
After:
```latex
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form a
subring. It contains the listed $s$, so also their sums $1$, $u^{\pm1}$
and $e_a$, which generate $R$. So $g\in Z(G)=\{1\}$.
```
Trade-off: the text now says why the ring generators lie in the subring. They are sums of the listed $s$, which uses the fact that $\mathcal P$ refines the letter partition.

## P14. l.194–203: commutator and corner (0 lines)
Before:
```latex
Set $k=[g,h]\in N\setminus\{1\}$ and $m=w+1$.
By~\eqref{eq:absorb}, both $k-I_3$ and $k^{-1}-I_3$ lie in
$M_3(B_m(U))$. If $e$ is the unit of $B_m(U)$, then
$k=(1-e)I_3+ek e$. Its corner part is invertible and therefore
corresponds to a locally constant function
\[
 \kappa:U\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1)\ge9.
\]
Choose nonempty clopen $W\subseteq U$ on which $\kappa$ is a constant
$\kappa_0\ne I_d$.
```
After:
```latex
Set $g_1=[g,h]\in K\setminus\{1\}$ and $m=w+1$.
By~\eqref{eq:absorb}, both $g_1-I_3$ and $g_1^{-1}-I_3$ lie in
$M_3(B_m(U))$, so $g_1=(1-e_V)I_3+e_Vg_1e_V$. The corner $e_Vg_1e_V$ is
invertible in $M_3(B_m(U))\cong M_d(\LC(U,\F_2))$, so it is a locally
constant function
\[
 \kappa:U\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1)\ge9.
\]
Choose a nonempty clopen $W\subseteq U$ on which $\kappa$ is a constant
$\kappa_0\ne I_d$.
```
Trade-off:
- "corresponds to" becomes the isomorphism it relies on.
- "therefore" goes.
- The renames resolve the $k$, $N$ and $e$ clashes.

## P15. l.205–215: transvections (−1 line)
Before:
```latex
Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
and as the identity elsewhere. It lies in $G$. Indeed, index its
coordinates by $(p,a)$, where $1\le p\le3$ and $|a|\le m$.
A transvection between $(p,a)$ and $(q,b)$ with $p\ne q$ is
$e_{pq}(E_{ab}(W))$. For $p=q$ and $a\ne b$, take $q\ne p$ and use
\[
 [e_{pq}(E_{ab}(W)),e_{qp}(E_{bb}(W))]
       =I_3+E_{ab}(W)E_{pp}.
\]
This follows from $E_{ab}E_{bb}=E_{ab}$ and $E_{bb}E_{ab}=0$.
These transvections generate $H_W$.
```
After:
```latex
Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
and as the identity elsewhere. It lies in $G$. Indeed, index its
coordinates by $(p,a)$, where $1\le p\le3$ and $|a|\le m$. For $p\ne q$,
the transvection between $(p,a)$ and $(q,b)$ is $e_{pq}(E_{ab}(W))$.
For $a\ne b$, the transvection between $(p,a)$ and $(p,b)$ is
\[
 [e_{pq}(E_{ab}(W)),e_{qp}(E_{bb}(W))]=I_3+E_{ab}(W)E_{pp}
\]
for any $q\ne p$, since $E_{ab}E_{bb}=E_{ab}$ and $E_{bb}E_{ab}=0$.
These transvections generate $H_W$.
```
Trade-off: the old sentence "For $p=q$ ..., take $q\ne p$" gave $q$ two values at once.

## P16. l.217–221: simplicity of H_W (0 lines)
Before:
```latex
Over $\F_2$, the group $\GL_d(\F_2)=\SL_d(\F_2)=\PSL_d(\F_2)$
is simple and centerless for $d\ge3$. Conjugation by $k$ on $H_W$
is conjugation by $\kappa_0$, so $[k,H_W]\subseteq N\cap H_W$
contains a nonidentity element. Since $N\cap H_W$ is normal in $H_W$,
we get $H_W\subseteq N$. In particular, $e_{12}(e_W)\in N$.
```
After:
```latex
The group $\GL_d(\F_2)=\PSL_d(\F_2)$ is simple and centerless for
$d\ge3$. Conjugation by $g_1$ acts on $H_W$ as conjugation by
$\kappa_0\ne I_d$, so $[g_1,H_W]\subseteq K\cap H_W$ is nontrivial.
Since $K\cap H_W$ is normal in $H_W$, we get $H_W\subseteq K$. In
particular $e_{12}(e_W)\in K$.
```
Trade-off:
- "Over $\F_2$" repeated the subscript.
- The middle term $\SL_d(\F_2)$ is not used anywhere.
- The renames apply here, and the comma after the short opener goes.

## P17. l.223–227: the level ideal (+1 line)
Before:
```latex
Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
After:
```latex
Finally, $I_K=\{r\in R:e_{12}(r)\in K\}$ is a two-sided ideal. If
$r\in I_K$, then $e_{ij}(r)\in K$ for all $i\ne j$, by conjugation with
the permutation matrices $e_{ij}(1)e_{ji}(1)e_{ij}(1)$, and
by~\eqref{eq:elementary} $I_K$ is closed under addition and under
multiplication by $R$ on either side. Since $0\ne e_W\in I_K$ and $R$
is simple, $I_K=R$, so $K=G$.\hfill$\square$
```
Trade-off:
- The permutation matrices are now named: over $\F_2$, $e_{12}(1)e_{21}(1)e_{12}(1)$ is the transposition matrix.
- "move", "gives", "Thus" and "completing the proof" go.

## P18. l.229–235: §2 title and corollary (0 lines)
Before:
```latex
\section{Every word-problem degree}

\begin{corollary}
Every Turing degree occurs as the word-problem degree of an infinite
simple Kazhdan LEF group. Consequently, there are continuum many
isomorphism classes of these groups.
\end{corollary}
```
After:
```latex
\section{Word problems}

\begin{corollary}\label{cor:degrees}
Every Turing degree is the word-problem degree of an infinite simple
Kazhdan LEF group. So there are continuum many isomorphism classes of
these groups.
\end{corollary}
```
Trade-off: the old title was a fragment, and "Consequently" becomes "So". The label is used by the optional sentence in part 1, E5.

## P19. l.238–249: the Turing reduction (+1 line)
Before:
```latex
The word problem of $G_X$, in the finite generators above, has the same
Turing degree as the language $L(X)$ of finite words occurring in $X$.
An oracle for $L(X)$ decides whether a matrix word equals $I_3$, by
checking the coefficient tables of its difference from $I_3$ on the
allowed windows. Conversely, for a word $v=v_0\cdots v_{n-1}$, the cylinder
indicator
\[
 e_{[v]}=\prod_{t=0}^{n-1}u^{-t}e_{v_t}u^t
\]
can be converted effectively, using~\eqref{eq:elementary}, to a group
word representing $e_{12}(e_{[v]})$. This word equals $1$ precisely
when $v\notin L(X)$.
```
After:
```latex
The word problem of $G_X$ with respect to the generators above has the
same Turing degree as the language $L(X)$ of finite words occurring in
$X$. Given $L(X)$, one decides whether a word in the generators equals
$I_3$ by computing the entries of the product and checking whether each
coefficient of its difference from $I_3$ vanishes on the words of $L(X)$
of the relevant length. Conversely, for a word $v=v_0\cdots v_{n-1}$, one
computes from~\eqref{eq:elementary} a word in the generators representing
$e_{12}(e_{[v]})$, where
\[
 e_{[v]}=\prod_{t=0}^{n-1}u^{-t}e_{v_t}u^t
\]
is the cylinder indicator of $v$. This word equals $1$ precisely when
$v\notin L(X)$.
```
Trade-off:
- "oracle" becomes the procedure, and the undefined "allowed windows" become the words of $L(X)$.
- "can be converted effectively" becomes active.
- A "matrix word" is now "a word in the generators".

## P20. l.251–261: Sturmian subshifts (0 lines; free shortening)
Before:
```latex
Now use the infinite minimal Sturmian subshift of an irrational slope
$\alpha\in(0,1)$~\cite{MorseHedlund}. Its language is computable from
$\alpha$: words of length $n$ are determined by the cyclic order of
the distinct rotation endpoints $-j\alpha\bmod1$, $0\le j\le n$.
Conversely, the minimum number of $1$'s in a word of length $n$ is
$\lfloor n\alpha\rfloor$, so the language computes $\alpha$.
Every Turing degree has an irrational representative: use $\sqrt2-1$
for the computable degree, and interleave the characteristic sequence
of a noncomputable set with $1$'s in a binary expansion for any other
degree. There are continuum many degrees, and the word-problem degree
of a finitely generated group is an isomorphism invariant.
```
After:
```latex
Now let $X_\alpha$ be the Sturmian subshift of an irrational slope
$\alpha\in(0,1)$, which is infinite and minimal~\cite{MorseHedlund}.
Its language is computable from $\alpha$: the words of length $n$ are
determined by the cyclic order of the points $-j\alpha\bmod1$,
$0\le j\le n$. Conversely, the minimum number of $1$'s in a word of
length $n$ is $\lfloor n\alpha\rfloor$, so $\alpha$ is computable from
$L(X_\alpha)$. Every Turing degree is the degree of an irrational
$\alpha\in(0,1)$: of $\sqrt2-1$ for the computable degree, and of
$\sum_{i\in S}2^{-i-1}$ for a noncomputable set $S$. There are
continuum many degrees, and the word-problem degree of a finitely
generated group is an isomorphism invariant.
```
Trade-off:
- Interleaving with 1's is unnecessary. A noncomputable $S$ has a binary expansion that is not eventually periodic, so $\sum_{i\in S}2^{-i-1}$ is irrational, lies in $(0,1)$, and has the degree of $S$ (irrational numbers have a unique binary expansion).
- "the language computes $\alpha$" (an anthropomorphism) becomes "$\alpha$ is computable from $L(X_\alpha)$".
- The object now has a name, $X_\alpha$.
- Please pass the interleaving observation to sk-word-problem and sk-referee-2.

## Line-count table (lines of the note; the doctrine sweep is at the end)
| item | lines | nature |
|---|---|---|
| E1 renames | 0 | clarity |
| E2 theorem | +1 | definition of LC; two sentences |
| E3 opening | +1 | count fix |
| E4 abstract | 0 | states the question |
| E5 intro paragraph | 0 (+2 optional) | metaphor, metacommentary, hyphen chains; optional corollary preview |
| E6 structure | 0 | moves l.78–82 and l.102–116 into "Simplicity" |
| E7 title, MSC | 0 | low priority |
| P1–P10 | −1 | l.69–152 |
| P11–P20 | +1 | l.154–262 |
| total | +2 (+4 with the optional E5 sentence) | |

**Doctrine sweep:** every hence/therefore/thus/consequently in l.31–233 is replaced within some item above.
- "Hence" l.99 → P3; l.113 → P5; l.143 → P9.
- "therefore" l.60 → E5; l.79 → P1; l.197 → P14.
- "Thus" l.77 → P1; l.116 → P5; l.149 → P10; l.227 → P17.
- "hence" l.31 → E4.
- "Consequently" l.233 → P18.
- The two "Indeed" sentences (l.124, l.206) are kept; they introduce justifications.
