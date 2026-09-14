# sk-open-6 proposal, part 2: finite models, towers, remaining edits, lengths, status

## (b2) Proof, second part: finite models

**Current, l.118-152** (from `\subsection*{Finite models}` through `\cite{Pestov}.`). **Replacement:**
```
\subsection*{Finite models}
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.

For each $k$ there is a periodic sequence $y=w^\infty$ with the same words
of length $2k+1$ as $x$, and its period $N$ can be chosen arbitrarily
large. Indeed, choose two occurrences in $x$ of a word of length $2k$
further apart than the length of a window that contains every word of
length $2k+1$, and let $w$ be the segment from the first to the second.
Repeating $w$ creates no new word of length $2k+1$ at the joins.

Let $\sigma_N$ be the cyclic shift of $\F_2^{\Z/N\Z}$, and define $D^y_P$ like
$D_P$ using the windows of $y$. For a fixed finite list of sums and
products in $R_x$, choose $k$ larger than all windows involved, including
those shifted in the products, and $N$ larger than twice every exponent of
$\sigma$ that occurs. The map
\[
  \sum_jD_{P_j}\sigma^j\longmapsto\sum_jD^y_{P_j}\sigma_N^j
\]
is well defined on the listed elements because $x$ and $y$ have the same
words of length $2k+1$. It preserves every listed operation, since
$\sigma D_P\sigma^{-1}=D_{P'}$ holds verbatim on the circle, and it keeps
nonzero elements nonzero, since the exponents stay distinct modulo $N$.

For a finite subset of $G$, include the entries of its elements, their
inverses, their differences, and all intermediate sums and products needed
for matrix multiplication. The resulting map is an injective partial
homomorphism into $\GL_{3N}(\F_2)$, so $G$ is LEF. The regular permutation
actions of these finite groups give sofic models; their permutation
matrices give hyperlinear models~\cite{Pestov}.
```
Verifier notes:
- Take occurrences p < p' of the same (2k)-word u with p' − p ≥ M, where every window of length M contains all (2k+1)-words, and set w = x_{[p,p')}.
- Every (2k+1)-window of w^∞ that meets one period lies in x_{[p,p'+2k)}. That segment has length at least M+2k, so it contains every word, and every word of it is a word of x.
- So the two sets of words are equal.
- The model is the note's construction, with D_y renamed D^y_P. Only the setting changed.

## (b3) Proof, third part: towers detect normal subgroups

**Current, l.154-227** (from `\subsection*{A finite tower detects every normal subgroup}` through `completing the proof.\hfill$\square$`). **Replacement:**
```
\subsection*{A finite tower detects every normal subgroup}
Let $v$ be a word of $x$ whose occurrences are more than $2m$ apart. For
$|a|,|b|\le m$ and a set $W$ of words of $x$ extending $v$ on both sides, put
\[
  E_{ab}(W)=\sigma^aD_W\sigma^{-b}.
\]
It maps $\delta_{n+b}$ to $\delta_{n+a}$ when a word of $W$ occurs at $n$, and
kills the other basis vectors. So
$E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$, and the span of these operators
is a subring $B_m(v)\cong M_{2m+1}(C_v)$, where $C_v$ is the commutative ring
spanned by the $D_W$. If the occurrences of $v$ are more than $2(m+w)$ apart
and $|i|,|j|\le w$, then
\begin{equation}\label{eq:absorb}
  \sigma^iD_P\,B_m(v)\,D_Q\sigma^j\subseteq B_{m+w}(v),
\end{equation}
because $\sigma^iD_PE_{ab}(W)D_Q\sigma^j=E_{a+i,b-j}(W')$ for a set $W'\subseteq W$.

Let $1\ne N\trianglelefteq G$ and choose $1\ne g\in N$. Let $w\ge0$ bound the
absolute exponents of $\sigma$ in the entries of $g$ and $g^{-1}$, and choose
$k$ so that the words of $x$ of length $2k+1$ have occurrences more than
$2w+2$ apart. Some matrix
\[
 h=e_{ij}(s),\qquad s\in\{D_v,\;D_v\sigma,\;D_v\sigma^{-1}\},
\]
with $v$ a word of $x$ of length $2k+1$, does not commute with $g$.
Otherwise, by~\eqref{eq:elementary}, the coefficients $s$ for which $g$
commutes with every $e_{ij}(s)$ form a subring containing
$\sigma^{\pm1}=\sum_vD_v\sigma^{\pm1}$ and every $D_a$, so $g\in Z(G)=\{1\}$.
Each such $s$ lies in $B_1(v)$: $D_v=E_{00}(v)$, $D_v\sigma=E_{0,-1}(v)$ and
$D_v\sigma^{-1}=E_{01}(v)$.

Set $c=[g,h]\in N\setminus\{1\}$ and $m=w+1$. By~\eqref{eq:absorb}, both
$c-I_3$ and $c^{-1}-I_3$ lie in $M_3(B_m(v))$. If $e$ is the unit of $B_m(v)$,
then $c=(1-e)I_3+ece$, and $ece$ is invertible in
$M_3(B_m(v))\cong M_d(C_v)$ with $d=3(2m+1)$. So there is a word $v'$ of $x$
extending $v$ on whose occurrences $ece$ acts by one matrix
$\kappa_0\in\GL_d(\F_2)$ with $\kappa_0\ne I_d$.

Let $H$ be the copy of $\GL_d(\F_2)$ acting on the tower over the occurrences
of $v'$ and as the identity elsewhere. It lies in $G$. Index its coordinates
by $(p,a)$ with $1\le p\le3$ and $|a|\le m$. The transvection from $(q,b)$ to
$(p,a)$ with $p\ne q$ is $e_{pq}(E_{ab}(v'))$, and these transvections
generate $\GL_d(\F_2)$ because $[t_{xz},t_{zy}]=t_{xy}$. The group
$\GL_d(\F_2)=\SL_d(\F_2)$ is simple and centerless for $d\ge3$. Conjugation by
$c$ on $H$ is conjugation by $\kappa_0$, so $[c,H]\subseteq N\cap H$ contains a
nonidentity element. So $H\subseteq N$, and in particular
$e_{12}(D_{v'})\in N$.

Finally, $I_N=\{r\in R_x:e_{12}(r)\in N\}$ is a two-sided ideal: permutation
matrices in $G$ move any elementary position to any other, and
\eqref{eq:elementary} gives addition and multiplication on either side by
arbitrary ring elements. Since $0\ne D_{v'}\in I_N$ and $R_x$ is simple,
$I_N=R_x$. So $N=G$, completing the proof.\hfill$\square$
```
Verifier notes:
- In σ^iD_P·σ^aD_Wσ^{-b}·D_Qσ^j, conjugating D_P and D_Q to the level of D_W gives σ^{a+i}D_{W'}σ^{-(b-j)}, where W' ⊆ W refines W by the windows of P and Q.
- The index range grows from 1 to 1+w. This needs occurrences of v more than 2(w+1) apart, which is the choice "more than 2w+2 apart", with m = w+1.
- The corner ece is a finite combination of D_W with bounded windows, so it is constant on the occurrences of a long enough extension v'. Since c ≠ I, some v' gives κ_0 ≠ I.
- For p = q, the transvection comes from [t_{(p,a),(q,c)}, t_{(q,c),(p,b)}] with q ≠ p, as in the current l.208-215 E_bb identity, but stated once in GL_d(F_2).
- The commutator is renamed k → c to avoid a clash with the window parameter k.

## (c) Remaining edits: introduction and corollary

**Current, l.55:** `The subshift algebra is classical; see Nekrashevych~\cite{Nekrashevych}.`
**Replacement:** `The ring $R_x$ is the algebraic crossed product of the orbit closure of $x$; see Nekrashevych~\cite{Nekrashevych}.`

**Current, l.60:** `supported on a clopen tower, and therefore contains an elementary`
**Replacement:** `supported on a tower over the occurrences of a word of $x$, and therefore contains an elementary`

**Current, l.238-239:** `The word problem of $G_X$, in the finite generators above, has the same Turing degree as the language $L(X)$ of finite words occurring in $X$.`
**Replacement:** `The word problem of $G_x$, in the finite generators above, has the same Turing degree as the set $L(x)$ of finite words occurring in $x$.`
Also replace `$L(X)$` by `$L(x)$` at l.240 and l.249.

**Current, l.242-248:**
```
allowed windows. Conversely, for a word $v=v_0\cdots v_{n-1}$, the cylinder
indicator
\[
 e_{[v]}=\prod_{t=0}^{n-1}u^{-t}e_{v_t}u^t
\]
can be converted effectively, using~\eqref{eq:elementary}, to a group
word representing $e_{12}(e_{[v]})$. This word equals $1$ precisely
```
**Replacement:**
```
allowed windows. Conversely, for a word $v=v_0\cdots v_{n-1}$, the operator
\[
 \prod_{t=0}^{n-1}\sigma^{-t}D_{v_t}\sigma^t,
\]
which multiplies $\delta_j$ by $[x_{[j,j+n)}=v]$, can be converted
effectively, using~\eqref{eq:elementary}, to a group word representing
$e_{12}$ of it. This word equals $1$ precisely
```

**Current, l.251-252:** `Now use the infinite minimal Sturmian subshift of an irrational slope $\alpha\in(0,1)$~\cite{MorseHedlund}. Its language is computable from $\alpha$:`
**Replacement:** `Now let $x_n=\lfloor(n+1)\alpha\rfloor-\lfloor n\alpha\rfloor$ be the Sturmian sequence of an irrational slope $\alpha\in(0,1)$, which is uniformly recurrent and not periodic~\cite{MorseHedlund}. Its language is computable from $\alpha$:`

The rest of the corollary proof (l.253-261) is unchanged.

## (d) Lengths and reader trade-off

| Block | Current lines | Proposed lines | Change |
|---|---|---|---|
| abstract l.28-34 | 7 | 8 | +1 |
| theorem l.44-53 + new remark | 10 | 21 | +11 |
| ring, (T), simplicity, centre l.69-116 | 48 | 44 | −4 |
| finite models l.118-152 | 35 | 30 | −5 |
| towers l.154-227 | 74 | 53 | −21 |
| introduction l.55, l.60 | — | — | 0 |
| corollary l.238-252 | — | — | +1 |
| **total** | | | **−17** |

Optional extra cut: the removed sentence at l.102-104 cited BCFS, Clark–Edie-Michell and Steinberg. If no other text cites them, their bibitems (about 15 lines) become unused. That call belongs with sk-cut-sentences, whose seed l.102-104 says to keep one of the two.

The remark after the theorem can shrink to its first two sentences (+3 instead of +12). That gives a net of −26 lines, at the cost of the equivalence with minimal subshifts and the necessity examples.

**Reader-facing trade-off (one sentence):** the theorem and its proof stay the same mathematics, but the group is now defined by two operators on F_2[Z]. The reader needs no subshifts, clopen sets, compactness or crossed products, the finite models are visibly the same construction on a circle, and the proof sections are 30 lines shorter. The price is a new ten-line remark connecting the statement to minimal subshifts.

Compatibility with seeds on main's order sheet (sk-arbitrary): the text already includes
- no translates (seed 2);
- the generator 1 dropped (seed 4);
- the single transvection sentence (seed 6);
- occurrences more than 2w+2 apart (seed 1);
- d ≥ 3 is all that is used (seed 3).

## (e) Status
- Bridge nodes, established and unreviewed:
  - `sequence-operator-ring-is-subshift-crossed-product` (+ `-proof`), landed ebe41a13a8;
  - `sequence-el3-simple-iff-uniformly-recurrent-aperiodic` (+ `-proof`), landed c10128755e.
- The pattern-language proof text (b1-b3) is unreviewed. It is queued with sk-referee-1.
- Points to check:
  - uniqueness of Σ D_{P_j}σ^j at a common window length;
  - the separated-occurrences lemma, which uses Morse–Hedlund p(L) ≥ L+1 for non-eventually-periodic x, and the fact that uniformly recurrent eventually periodic sequences are periodic;
  - the well-definedness of the circle model on representatives;
  - the corner-constancy step that produces v'.
- No credit wording is changed. The lineage sentence and the origin paragraph are untouched.
