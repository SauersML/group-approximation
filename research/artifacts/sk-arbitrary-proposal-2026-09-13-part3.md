# sk-arbitrary proposal, part 3: combined candidate text (2026-09-13)

This text applies A1–A7, A10 and A11 from parts 1–2 to l.94-116 and l.154-227 of `$SK/manuscript-disk-1646.tex`.
- A8 (EL_n) is NOT applied here, so the items stay separable. Its substitutions are listed in part 2.
- Lines not shown are unchanged.
- Status: unreviewed.

## Replacement for l.94-116 (end of "The ring and property (T)")
```
show that the matrices $e_{ij}(s)$, for
$s\in\{u,u^{-1}\}\cup\{e_a:a\in A\}$, generate $G$.
Ershov--Jaikin-Zapirain's theorem says that $\EL_n(R)$ has property~(T)
for every finitely generated unital associative ring $R$ and
$n\ge3$~\cite[Theorem~1.1]{EJZ}. Hence $G$ has property~(T).
It is infinite because $e_{12}(\LC(X,\F_2))$ is infinite.

We will also need that $Z(R)=\F_2$. If $r=\sum_jf_ju^j$ is central,
commuting with all clopen indicators forces $f_j=0$
for $j\ne0$: otherwise a point in the support of $f_j$ and its
$T^{-j}$-translate can be separated by a clopen set. Commuting with
$u$ then makes $f_0$ invariant, hence constant by minimality.
Finally, commuting with every $e_{ij}(1)$ forces a central element of
$G$ to be $cI_3$; commuting with all $e_{ij}(r)$ gives
$c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$.
```
(l.97-100 are kept verbatim. The prose doctrine prefers "so" to "Hence", but that is user prose and is not changed here.)

## Replacement for l.154-227 ("A finite tower detects every normal subgroup")
```
\subsection*{A finite tower detects every normal subgroup}
Let $U$ be clopen with $U\cap T^jU=\varnothing$ for $0<|j|\le2m$.
For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
$E_{ab}(W)=u^ae_Wu^{-b}$. Then
$E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$, so their span is a subring
\[
  B_m(U)\cong M_{2m+1}(\LC(U,\F_2)),
\]
with unit $\sum_{|a|\le m}E_{aa}(U)$. If $r,r'$ involve only powers
$u^j$ with $|j|\le w$, and $U\cap T^jU=\varnothing$ for $0<|j|\le2(m+w)$, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U),
\end{equation}
since $fu^iE_{ab}(W)=u^{a+i}(u^{-a-i}fu^{a+i})e_Wu^{-b}=E_{a+i,b}(W_1)$
for a clopen $W_1\subseteq W$, and similarly on the right.

Let $1\ne N\trianglelefteq G$, and choose $1\ne g\in N$.
Let $w\ge0$ bound the absolute values of the exponents in all entries
of $g$ and $g^{-1}$, and put $m=w+1$.
Choose a finite clopen partition $\mathcal P$ refining the letter
partition, with $C\cap T^jC=\varnothing$ for $C\in\mathcal P$ and
$0<|j|\le2m$. Some matrix
\[
 h=e_{ij}(s),\qquad
 s\in\{e_C,e_Cu,e_Cu^{-1}:C\in\mathcal P\},
\]
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
a subring containing all ring generators, so $g\in Z(G)=\{1\}$.
Since $e_C=E_{00}(C)$ and $e_Cu^{\pm1}=E_{0,\mp1}(C)$, we have $s\in B_1(C)$.
Set $g'=[g,h]\in N\setminus\{1\}$.
By~\eqref{eq:absorb}, both $g'-I_3$ and $g'^{-1}-I_3$ lie in
$M_3(B_m(C))$. If $e$ is the unit of $B_m(C)$, then
$g'=(1-e)I_3+eg'e$. Its corner part is invertible and therefore
corresponds to a locally constant function
\[
 \kappa:C\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1).
\]
Choose nonempty clopen $W\subseteq C$ on which $\kappa$ is a constant
$\kappa_0\ne I_d$.

Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
and as the identity elsewhere. Index its coordinates by $(p,a)$, where
$1\le p\le3$ and $|a|\le m$. The transvections $e_{pq}(E_{ab}(W))$ with
$p\ne q$ lie in $G$, and their commutators give the remaining
transvections, so $H_W\subseteq G$.

Over $\F_2$, the group $\GL_d(\F_2)=\SL_d(\F_2)=\PSL_d(\F_2)$
is simple and centerless for $d\ge3$. Conjugation by $g'$ on $H_W$
is conjugation by $\kappa_0$, so $[g',H_W]\subseteq N\cap H_W$
contains a nonidentity element. Since $N\cap H_W$ is normal in $H_W$,
we get $H_W\subseteq N$. In particular, $e_{12}(e_W)\in N$.

Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. It contains $e_W$, hence every
$u^ne_Wu^{-n}=e_{T^nW}$. Finitely many of these cover $X$, so
$1=1-\prod_i(1-e_{T^{n_i}W})$ lies in $I_N$. Thus $N=G$,
completing the proof.\hfill$\square$
```

## Checks on the combined text
- (eq:absorb) as used: s ∈ B_1(C), and the entries of g, g^{-1} have exponents ≤ w. The hypothesis "C ∩ T^jC = ∅ for 0<|j| ≤ 2(1+w) = 2m" is exactly the partition condition.
  - g' − I = (g sE_ij g^{-1} − sE_ij)h^{-1}. Its entries are sums of r s r' (in B_m(C)) and s, multiplied inside the ring B_m(C).
  - g'^{-1} − I = h(g(−sE_ij)g^{-1} + sE_ij), in the same way.
- H_W: for q ≠ p and a ≠ b, [e_pq(E_ab(W)), e_qp(E_bb(W))] = I + E_ab(W)E_pp, which is the transvection between (p,a) and (p,b). Transvections generate GL_d(F_2) = SL_d(F_2).
- Covering: X is minimal and W is nonempty and open, so ∪_n T^nW = X, and compactness gives finitely many n_i.
- Line count: the l.154-227 block goes from 74 lines to about 60; the l.102-110 block goes from 9 lines to 2.

## Bibliography effect
If A10 is taken without the context clause, `\cite{BCFS,ClarkEdie,Steinberg}` disappears from the text, and those three bibitems become unused (−15 bibliography lines). That is for the user and sk-citations to decide.
