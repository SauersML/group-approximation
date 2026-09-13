# sk-simplicity-short-a: a shorter simplicity proof for the note (proposal, part 1 of 2)

- Lane: sk-simplicity-short-a, 2026-09-13.
- Status: UNREVIEWED, queued with sk-referee-1.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).
- Cairn: route `subshift-elementary-group-simple-constant-tower-proof` (all q), into the established claim `subshift-elementary-group-is-simple-modulo-centre`.
- Part 2 has the sentence-by-sentence check and the all-q version.

## What changes
The simplicity section, l.154-227 (74 lines), becomes 47 lines. The centres of R and G, l.110-116 (7 lines), are no longer needed. Three observations do it.

1. **Only the roots e_ij(e_C) are needed.** Over F_2 the only unit of LC(X,F_2) is 1, so a nontrivial g ∈ N already fails to commute with some h = e_ij(e_C), where C is an atom of a partition with disjoint levels. This removes:
   - the subring argument (l.185-187);
   - the three root shapes e_C, e_Cu, e_Cu^{-1} (l.189-193);
   - the computation of Z(R) and Z(G) (l.110-116). Z(G) = 1 then follows from simplicity, since G is nonabelian.
2. **k lands in one finite group.** Refine the partition so that all coefficients of the entries of g and g^{-1} are constant on the levels T^aC, |a| ≤ w. Then k = [g,h] lies in a single finite group H ≅ GL_d(F_2) over the tower of C, and N ∩ H contains k itself. This removes:
   - the locally constant κ: U → GL_d(F_2);
   - the piece W;
   - the conjugation-by-κ_0 step (l.196-203, l.217-220).
3. **The tower is smaller.** It has height w, because h sits at level 0. The absorption display (eq:absorb) shrinks to one product formula. A transvection inside one column p is a commutator through a third column r ≠ p, by identity (1) inside GL_d(F_2) itself, so the hand computation l.209-214 goes.

The level-ideal step stays. J is defined through all positions p ≠ q, so the permutation-matrix remark (l.224) goes too.

## (a) Current text and replacement

### A. The ring paragraph, l.102-116
Current (verbatim, with line numbers):
```text
102  We will also need that $R$ is simple and $Z(R)=\F_2$.
103  These are standard groupoid-algebra facts~\cite{BCFS,ClarkEdie,Steinberg};
104  here is the direct argument. A nonzero two-sided ideal contains an
105  element $r=\sum_j f_ju^j$ with $f_0\ne0$, after multiplication by a
106  power of $u$. Choose a nonempty clopen $U$ on which $f_0=1$, disjoint
107  from $T^jU$ for every nonzero exponent occurring in $r$. Then
108  $e_Ure_U=e_U$. Finitely many translates of $U$ cover $X$, so the ideal
109  contains $1=1-\prod_i(1-e_{T^{n_i}U})$.
110  If $r$ is central, commuting with all clopen indicators forces $f_j=0$
111  for $j\ne0$: otherwise a point in the support of $f_j$ and its
112  $T^{-j}$-translate can be separated by a clopen set. Commuting with
113  $u$ then makes $f_0$ invariant, hence constant by minimality.
114  Finally, commuting with every $e_{ij}(1)$ forces a central element of
115  $G$ to be $cI_3$; commuting with all $e_{ij}(r)$ gives
116  $c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$.
```

Replacement:
- replace l.102-104 by the three lines below;
- keep l.105-109 unchanged;
- delete l.110-116.

```latex
We will also need that $R$ is simple.
This is a standard groupoid-algebra fact~\cite{BCFS,ClarkEdie,Steinberg};
here is the direct argument. A nonzero two-sided ideal contains an
```

### B. The simplicity section, l.154-227
Current (verbatim, with line numbers):
```text
154  \subsection*{A finite tower detects every normal subgroup}
155  Suppose the levels $T^aU$ are disjoint for all indices needed below.
156  For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
157  \[
158    E_{ab}(W)=e_{T^aW}u^{a-b}.
159  \]
160  These satisfy
161  $E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$.
162  Their span is a subring
163  \[
164    B_m(U)\cong M_{2m+1}(\LC(U,\F_2)),
165  \]
166  with unit $e_{\bigcup_{|a|\le m}T^aU}$. If $r,r'$ involve only powers
167  $u^j$ with $|j|\le w$, then
168  \begin{equation}\label{eq:absorb}
169    r B_m(U)r'\subseteq B_{m+w}(U),
170  \end{equation}
171  provided the larger tower is disjoint. To see this, multiplying
172  $E_{ab}(W)$ on the left by $fu^i$ and on the right by $f'u^j$ changes
173  its indices to $(a+i,b-j)$ and restricts its clopen coefficient.
174  
175  Let $1\ne N\trianglelefteq G$, and choose $1\ne g\in N$.
176  Let $w\ge0$ bound the absolute values of the exponents in all entries
177  of $g$ and $g^{-1}$.
178  Choose a finite clopen partition $\mathcal P$ refining the letter
179  partition, with $C\cap T^jC=\varnothing$ for $C\in\mathcal P$ and
180  $0<|j|\le2w+3$. Some matrix
181  \[
182   h=e_{ij}(s),\qquad
183   s\in\{e_C,e_Cu,e_Cu^{-1}:C\in\mathcal P\},
184  \]
185  does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
186  coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
187  a subring containing all ring generators, so $g\in Z(G)=\{1\}$.
188  
189  Each such $s$ lies in $B_1(U)$ for a translate $U$ of $C$:
190  \[
191   e_C=E_{00}(C),\quad e_Cu=E_{10}(T^{-1}C),\quad
192   e_Cu^{-1}=E_{-1,0}(TC).
193  \]
194  Set $k=[g,h]\in N\setminus\{1\}$ and $m=w+1$.
195  By~\eqref{eq:absorb}, both $k-I_3$ and $k^{-1}-I_3$ lie in
196  $M_3(B_m(U))$. If $e$ is the unit of $B_m(U)$, then
197  $k=(1-e)I_3+ek e$. Its corner part is invertible and therefore
198  corresponds to a locally constant function
199  \[
200   \kappa:U\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1)\ge9.
201  \]
202  Choose nonempty clopen $W\subseteq U$ on which $\kappa$ is a constant
203  $\kappa_0\ne I_d$.
204  
205  Let $H_W$ be the copy of $\GL_d(\F_2)$ acting on the tower over $W$
206  and as the identity elsewhere. It lies in $G$. Indeed, index its
207  coordinates by $(p,a)$, where $1\le p\le3$ and $|a|\le m$.
208  A transvection between $(p,a)$ and $(q,b)$ with $p\ne q$ is
209  $e_{pq}(E_{ab}(W))$. For $p=q$ and $a\ne b$, take $q\ne p$ and use
210  \[
211   [e_{pq}(E_{ab}(W)),e_{qp}(E_{bb}(W))]
212         =I_3+E_{ab}(W)E_{pp}.
213  \]
214  This follows from $E_{ab}E_{bb}=E_{ab}$ and $E_{bb}E_{ab}=0$.
215  These transvections generate $H_W$.
216  
217  Over $\F_2$, the group $\GL_d(\F_2)=\SL_d(\F_2)=\PSL_d(\F_2)$
218  is simple and centerless for $d\ge3$. Conjugation by $k$ on $H_W$
219  is conjugation by $\kappa_0$, so $[k,H_W]\subseteq N\cap H_W$
220  contains a nonidentity element. Since $N\cap H_W$ is normal in $H_W$,
221  we get $H_W\subseteq N$. In particular, $e_{12}(e_W)\in N$.
222  
223  Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
224  permutation matrices in $G$ move any elementary position to any other,
225  and~\eqref{eq:elementary} gives addition and multiplication on either
226  side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
227  simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```

Replacement, verbatim LaTeX. It uses only what the note defines before l.154:
- `e_U`, `u`, `e_{ij}(r)`, the matrix units `E_{ij}`, `\eqref{eq:elementary}`, `\LC`, `\GL`, `\PSL`;
- the compactness remark l.78-82, which supplies the partition.

```latex
\subsection*{A finite tower detects every normal subgroup}
Let $1\ne N\trianglelefteq G$ and $1\ne g\in N$. Let $w\ge0$ bound the
absolute values of the exponents in all entries of $g$ and $g^{-1}$.
Choose a finite clopen partition $\mathcal P$ such that, for each
$C\in\mathcal P$, the sets $T^aC$ with $|a|\le w$ are pairwise disjoint
and all coefficients of the entries of $g$ and $g^{-1}$ are constant on
each of them.

Some $h=e_{ij}(e_C)$ with $C\in\mathcal P$ does not commute with $g$.
Otherwise $g$ commutes with every $e_{ij}(1)=\prod_Ce_{ij}(e_C)$, so
$g=cI_3$ with $c=\sum_jc_ju^j\in R$. Comparing coefficients in
$ce_C=e_Cc$ shows that $c_j$ vanishes on $C\cup T^jC$ for every
$C\in\mathcal P$ and $0<|j|\le w$. So $c\in\LC(X,\F_2)$, and the constant
coefficient of $cc^{-1}=1$ gives $c=1$, a contradiction.

Fix such $h$ and put $k=[g,h]\in N\setminus\{1\}$. For $|a|,|b|\le w$ put
$\epsilon_{ab}=e_{T^aC}u^{a-b}$. Since the levels $T^aC$ are disjoint,
$\epsilon_{ab}\epsilon_{cd}=\delta_{bc}\epsilon_{ad}$, so these elements
span a subring $B\cong M_{2w+1}(\F_2)$ with unit $e=\sum_a\epsilon_{aa}$.
If $|i|,|j|\le w$ and $f,f'\in\LC(X,\F_2)$ are constant on $T^iC$ and on
$C$, respectively, then $fu^ie_Cf'u^j\in\{0,\epsilon_{i,-j}\}$. So
\[
  y=ghg^{-1}-h=g\,e_CE_{ij}\,g^{-1}-e_CE_{ij}\in M_3(B).
\]
As $h^{-1}=h$, both $k-I_3=yh$ and $k^{-1}-I_3=hy$ lie in $M_3(B)$. So
$k=(1-e)I_3+x$ with $x=eI_3+k-I_3$ invertible in $M_3(B)$, that is, $k$
lies in the group
\[
  H=\{(1-e)I_3+x:x\in\GL_3(B)\}\cong\GL_d(\F_2),\qquad d=3(2w+1).
\]

The group $H$ lies in $G$. Index the coordinates of $M_3(B)$ by pairs
$(p,a)$ with $1\le p\le3$ and $|a|\le w$. The transvection of $H$ between
$(p,a)$ and $(q,b)$ is $I_3+\epsilon_{ab}E_{pq}$. For $p\ne q$ it is the
elementary matrix $e_{pq}(\epsilon_{ab})$. For $p=q$ it is the commutator
of the transvections between $(p,a)$ and $(r,a)$ and between $(r,a)$ and
$(p,b)$, where $r\ne p$. These transvections generate $H$.

The group $\GL_d(\F_2)=\PSL_d(\F_2)$ is simple for $d\ge3$. As $N\cap H$
is normal in $H$ and contains $k$, we get $H\subseteq N$. In particular
$e_{pq}(e_C)=e_{pq}(\epsilon_{00})\in N$ for all $p\ne q$.

Finally $J=\{r\in R:e_{pq}(r)\in N\text{ for all }p\ne q\}$ is a two-sided
ideal. It is additive by~\eqref{eq:elementary}, and if $l$ is the third
index, then $e_{pq}(sr)=[e_{pl}(s),e_{lq}(r)]$ and
$e_{pq}(rs)=[e_{pl}(r),e_{lq}(s)]$. Since $0\ne e_C\in J$ and $R$ is
simple, $J=R$. So $N=G$, completing the proof.\hfill$\square$
```

## (b) Proof text
The replacement above is the complete text of the section as it would appear. Besides (1), its only input from earlier in the note is the ring-simplicity argument l.104-109, which is unchanged.

## (c) Length
- l.154-227 (74 lines) becomes 47 lines.
- l.110-116 (7 lines) are deleted. l.102-104 are reworded at the same length.
- Net change: -34 lines in the note (340 → 306).

## (d) Reader-facing trade-off
Shorter, with the same rigor, and with no new machinery or unverified fact.
- The reader follows one finite group H ≅ GL_d(F_2) that contains the commutator k itself. The current text needs a locally constant function U → GL_d(F_2), a piece W, and a conjugation argument.
- The reader no longer reads the centres of R and G, which the proof does not use.

## (e) Status
- UNREVIEWED. The review request is in `$SK/queue/sk-referee-1.txt`.
- Cairn: route `subshift-elementary-group-simple-constant-tower-proof`.
  - Target: the established claim `subshift-elementary-group-is-simple-modulo-centre` (the all-q statement).
  - Requires: `minimal-subshift-algebra-is-simple-lef-ring` (simplicity of R).
- Part 2 §1 checks every sentence of the replacement, and §2 gives the all-q version.
- Peers:
  - sk-simplicity-short-b: independent start on the same question.
  - sk-proof-minimal-concrete: its whole-proof rewrite may absorb this text.
  - sk-coefficients: part 2 §2 is the F_q version, including the scalar case.
