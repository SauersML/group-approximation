# sk-simplicity-short-b proposal: simplicity in one commutator (2026-09-13)

Lane sk-simplicity-short-b. Status: unreviewed, review requested from sk-referee-1.
Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).
Cairn: `binary-subshift-normal-subgroups-contain-tower-gl-copy` with route `-proof` (`requires: []`).

## The idea
Let w bound the exponents in g^{±1}. Choose the clopen set V so small that:
- its first 2w translates are disjoint;
- every coefficient f of an entry of g^{±1} has f∘T^i constant on V for |i| ≤ w.

Then each product f u^i e_V f' u^j is 0 or a tower matrix unit E_{i,−j}. So the commutator k = [g, e_ij(e_V)] already lies in one finite copy H_V ≅ GL_d(F_2), d = 3(2w+1), and simplicity of GL_d(F_2) puts H_V inside N.

This removes:
- the tower subrings B_m(U) ≅ M_{2m+1}(LC(U,F_2)) and the absorption identity;
- the locally constant function κ and the choice of W;
- the subring argument with the letter partition;
- the p = q commutator display;
- the "I_N is an ideal" step with permutation matrices;
- the separate proofs that R is simple and that Z(R) = F_2.

## (a) Current text and replacement

### 1. Delete l.78-82
```
Minimality and infiniteness imply that $T$ has no periodic points.
For each $L$, every point therefore has a clopen neighborhood $U$ with
$U\cap T^jU=\varnothing$ for $0<|j|\le L$. Compactness gives finite
clopen partitions with this property, refining any prescribed clopen
partition.
```
The first sentence moves into the new subsection. The LEF and word-problem parts use none of this.

### 2. Delete l.101-116 (the blank l.101 and the paragraph l.102-116)
```
We will also need that $R$ is simple and $Z(R)=\F_2$.
These are standard groupoid-algebra facts~\cite{BCFS,ClarkEdie,Steinberg};
here is the direct argument. A nonzero two-sided ideal contains an
element $r=\sum_j f_ju^j$ with $f_0\ne0$, after multiplication by a
power of $u$. Choose a nonempty clopen $U$ on which $f_0=1$, disjoint
from $T^jU$ for every nonzero exponent occurring in $r$. Then
$e_Ure_U=e_U$. Finitely many translates of $U$ cover $X$, so the ideal
contains $1=1-\prod_i(1-e_{T^{n_i}U})$.
If $r$ is central, commuting with all clopen indicators forces $f_j=0$
for $j\ne0$: otherwise a point in the support of $f_j$ and its
$T^{-j}$-translate can be separated by a clopen set. Commuting with
$u$ then makes $f_0$ invariant, hence constant by minimality.
Finally, commuting with every $e_{ij}(1)$ forces a central element of
$G$ to be $cI_3$; commuting with all $e_{ij}(r)$ gives
$c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$.
```
Neither fact is needed now:
- The new proof shows R e_V R = R in one line, from the covering by translates.
- A simple nonabelian group has trivial centre.

### 3. Replace l.154-227
```
\subsection*{A finite tower detects every normal subgroup}
Suppose the levels $T^aU$ are disjoint for all indices needed below.
For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
\[
  E_{ab}(W)=e_{T^aW}u^{a-b}.
\]
These satisfy
$E_{ab}(W)E_{cd}(W')=\delta_{bc}E_{ad}(W\cap W')$.
Their span is a subring
\[
  B_m(U)\cong M_{2m+1}(\LC(U,\F_2)),
\]
with unit $e_{\bigcup_{|a|\le m}T^aU}$. If $r,r'$ involve only powers
$u^j$ with $|j|\le w$, then
\begin{equation}\label{eq:absorb}
  r B_m(U)r'\subseteq B_{m+w}(U),
\end{equation}
provided the larger tower is disjoint. To see this, multiplying
$E_{ab}(W)$ on the left by $fu^i$ and on the right by $f'u^j$ changes
its indices to $(a+i,b-j)$ and restricts its clopen coefficient.

Let $1\ne N\trianglelefteq G$, and choose $1\ne g\in N$.
Let $w\ge0$ bound the absolute values of the exponents in all entries
of $g$ and $g^{-1}$.
Choose a finite clopen partition $\mathcal P$ refining the letter
partition, with $C\cap T^jC=\varnothing$ for $C\in\mathcal P$ and
$0<|j|\le2w+3$. Some matrix
\[
 h=e_{ij}(s),\qquad
 s\in\{e_C,e_Cu,e_Cu^{-1}:C\in\mathcal P\},
\]
does not commute with $g$. Otherwise, by~\eqref{eq:elementary}, the
coefficients $s$ for which $g$ commutes with every $e_{ij}(s)$ form
a subring containing all ring generators, so $g\in Z(G)=\{1\}$.

Each such $s$ lies in $B_1(U)$ for a translate $U$ of $C$:
\[
 e_C=E_{00}(C),\quad e_Cu=E_{10}(T^{-1}C),\quad
 e_Cu^{-1}=E_{-1,0}(TC).
\]
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

Over $\F_2$, the group $\GL_d(\F_2)=\SL_d(\F_2)=\PSL_d(\F_2)$
is simple and centerless for $d\ge3$. Conjugation by $k$ on $H_W$
is conjugation by $\kappa_0$, so $[k,H_W]\subseteq N\cap H_W$
contains a nonidentity element. Since $N\cap H_W$ is normal in $H_W$,
we get $H_W\subseteq N$. In particular, $e_{12}(e_W)\in N$.

Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
by (this is also the complete proof text, (b)):
```
\subsection*{Simplicity}
Let $1\ne N\trianglelefteq G$ and $1\ne g\in N$, and let $w\ge0$ bound
the absolute values of the exponents in the entries of $g$ and $g^{-1}$.
Call a clopen set $V$ small if $V\cap T^jV=\varnothing$ for
$0<|j|\le2w$ and every function $f\circ T^i$, with $|i|\le w$ and $f$ a
coefficient of an entry of $g$ or $g^{-1}$, is constant on $V$.
Minimality and infiniteness imply that $T$ has no periodic points, so
every point has a small clopen neighborhood, and by compactness every
clopen set is a finite disjoint union of small ones.

Some $h=e_{ij}(e_V)$ with $V$ small and nonempty does not commute
with $g$. Otherwise, by~\eqref{eq:elementary}, $g$ commutes with
$e_{ij}(e_V)$ for every clopen $V$. Taking $V=X$ gives $g=cI_3$ with
$c=\sum_jf_ju^j\in R$, and then $e_Vc-ce_V=\sum_jf_j(e_V-e_{T^jV})u^j$
vanishes for every $V$. If $f_j(x)=1$ for some $j\ne0$, a clopen $V$
containing $x$ but not $T^{-j}x$ contradicts this. So
$c\in\LC(X,\F_2)^\times=\{1\}$, and $g=1$.

Fix such $h$ and $V$, and put $d=3(2w+1)$. For $|a|,|b|\le w$ the
elements $E_{ab}=e_{T^aV}u^{a-b}$ satisfy
$E_{ab}E_{cd}=\delta_{bc}E_{ad}$. Index the coordinates of $\F_2^d$ by
pairs $(p,a)$ with $1\le p\le3$ and $|a|\le w$. Then
$E_{(p,a),(q,b)}\mapsto E_{ab}E_{pq}$ defines a multiplicative map
$\varphi:M_d(\F_2)\to M_3(R)$, and $A\mapsto I_3-\varphi(I_d)+\varphi(A)$
embeds $\GL_d(\F_2)$ in $\GL_3(R)$. Its image $H_V$ lies in $G$, because
$\GL_d(\F_2)$ is generated by the transvections between $(p,a)$ and
$(q,b)$ with $p\ne q$ (the others are commutators of these), and these
map to $e_{pq}(E_{ab})$.

Put $k=[g,h]\in N\setminus\{1\}$. For $f,f'$ as above and $|i|,|j|\le w$,
\[
  fu^i\,e_V\,f'u^j=f\,e_{T^iV}\,(f'\circ T^{-i})\,u^{i+j}
  \in\{0,E_{i,-j}\},
\]
since $f\circ T^i$ and $f'$ are constant on $V$. The entries of
$ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$ are sums of such products, and
$h^{-1}=h=I_3+E_{00}E_{ij}$. So $k-I_3$ and $k^{-1}-I_3$ lie in
$\varphi(M_d(\F_2))$, and $k\in H_V$. Then $N\cap H_V$ is a nontrivial
normal subgroup of $H_V\cong\GL_d(\F_2)=\PSL_d(\F_2)$, which is simple
because $d\ge3$. So $H_V\subseteq N$, and $e_{pq}(e_V)\in N$ for $p\ne q$.

For distinct $i,j,l$ and $r,s\in R$, \eqref{eq:elementary} gives
$e_{il}(re_V)=[e_{ij}(r),e_{jl}(e_V)]\in N$ and then
$e_{ij}(re_Vs)=[e_{il}(re_V),e_{lj}(s)]\in N$. By minimality finitely
many translates $T^nV$ cover $X$. Since $e_{T^nV}=u^ne_Vu^{-n}$, the
identity $1=1-\prod_n(1-e_{T^nV})$ writes $1$, and so every element
of $R$, as a sum of products $re_Vs$. So $N$ contains every $e_{ij}(r)$,
and $N=G$.\hfill$\square$
```

### 4. Optional: bibliography
After deletion 2, `\cite{BCFS,ClarkEdie,Steinberg}` no longer appears anywhere. Either:
- delete those three bibitems (l.278-289 and l.323-327, 17 lines); or
- keep them by adding them to the sentence at l.55 ("The subshift algebra is classical; see ...").

That is a credit call for the user. Default: delete, since nothing in the note uses ring simplicity any more.

## (c) Length
- Removed: 74 lines (l.154-227), 5 lines (l.78-82), 16 lines (l.101-116), 95 in total.
- Added: 48 lines.
- Net: −47 lines, from 340 to 293. With the optional bibliography deletion, −64 lines.
- `\label{eq:absorb}` disappears; nothing else references it (checked: only l.168, l.195).

## (d) Reader-facing trade-off
- Shorter by 47 lines, with the same theorem and no new machinery.
- The reader follows one commutator into one finite copy of GL_d(F_2). There are no tower subrings, no locally constant GL_d-valued function, no subring argument, and no separate ring-simplicity or centre lemmas.
- The only facts the reader must trust are textbook ones: GL_d(F_2) is simple for d ≥ 3 and generated by transvections, plus the elementary identities already displayed at l.87-93.

## (e) Status
- Claim `binary-subshift-normal-subgroups-contain-tower-gl-copy`, route `binary-subshift-normal-subgroups-contain-tower-gl-copy-proof` (`requires: []`): unreviewed. The review line is appended to `$SK/queue/sk-referee-1.txt`.
- It sits beside the on-main `subshift-elementary-group-is-simple-modulo-centre` (every q, modulo the centre, with a scalar case) and does not replace it.

## Checks a verifier should redo
1. **E_ab E_cd = δ_bc E_ad.** u^{a−b} e_{T^cV} = e_{T^{a−b+c}V} u^{a−b}, so the product is e_{T^aV ∩ T^{a−b+c}V} u^{a−b+c−d}. For b = c it is E_ad. For b ≠ c the set is T^a(V ∩ T^{c−b}V) = ∅, since 0 < |c−b| ≤ 2w.
2. **Absorption.** u^i f' = (f'∘T^{−i}) u^i with the note's convention u f u^{−1} = f∘T^{−1}. The coefficient f · 1_{T^iV} · (f'∘T^{−i}) takes the value f(T^ix) f'(x) at T^ix, for x ∈ V. Both factors are constant on V, so it is 0 or 1_{T^iV}. This gives 0 or e_{T^iV}u^{i+j} = E_{i,−j}, with |−j| ≤ w.
3. **Entries of g e_V E_ij g^{−1}.** The (p,q) entry is g_{pi} e_V (g^{−1})_{jq} = Σ_{t,s} f_t u^t e_V f'_s u^s ∈ span{E_ab}. The span of E_ab E_pq is φ(M_d(F_2)) and is closed under products.
4. **k ∈ H_V.**
   - k = (I+Y)h and k^{−1} = h(I+Y), because h^{−1} = h.
   - Both lie in I + φ(M_d), say I + φ(X) and I + φ(X').
   - (I+φX)(I+φX') = I and φ is injective, so (I_d+X)(I_d+X') = I_d.
   - So k is the image of I_d + X ∈ GL_d(F_2).
5. **The map A ↦ I − φ(I_d) + φ(A) is a homomorphism.** φ(I_d) is idempotent and φ(A) = φ(I_d)φ(A)φ(I_d). The image of I_d + E_{(p,a),(q,b)} is I + E_ab E_pq = e_pq(E_ab).
6. **Transvection generation.** For a ≠ b, I + E_{(p,a),(p,b)} = [I + E_{(p,a),(q,c)}, I + E_{(q,c),(p,b)}] with q ≠ p, a commutator of three distinct indices.
7. **Non-commuting h.** The pieces of a clopen V are small, so e_ij(e_V) is a product of e_ij(e_{V_t}) over small V_t.
   - Commuting with every e_ij(1) forces a scalar matrix cI_3.
   - The u^j coefficient of e_Vc − ce_V is f_j(e_V − e_{T^jV}). Its value at x is f_j(x)(1_V(x) − 1_V(T^{−j}x)).
   - T^{−j}x ≠ x because T has no periodic points, so a clopen V separates x from T^{−j}x.
   - So c = f_0 lies in LC(X,F_2)^× = {1}.
8. **Spreading.** [e_ik(r), e_kj(s)] = e_ij(rs) with (i,k,j) = (i,j,l), then (i,l,j). A commutator with one factor in N lies in N. 1 − Π(1 − e_{T^nV}) = 0 on the complement of the union, i.e. everywhere, and its expansion is a sum of products each containing some e_{T^nV} = u^n e_V u^{−n}.
9. **d = 3(2w+1) ≥ 3 for every w ≥ 0.** GL_3(F_2) ≅ PSL_2(7) is simple, so the case w = 0 also works.

## Tried and discarded
- **Avoiding the simplicity of GL_d(F_2).** Extracting a transvection from a non-central κ_0 by hand (the Artin two-commutator argument) takes more lines than the one-line citation. So the citation stays.
- **Choosing h with u-coefficients**, as the current text does. That forces the letter partition, height 2w+3 and m = w+1. The small-clopen-set h needs only height 2w and gives d = 3(2w+1).
- **Merging extraction with the level ideal.** Once H_V ⊆ N, the two-commutator spreading step is shorter than defining I_N and checking it is an ideal with permutation matrices. So the merge is exactly the last paragraph.

## Note for other lanes (sk-coefficients, sk-proof-minimal-*)
The binary shortcut uses two features of F_2:
- LC(X,F_2)^× = {1}, so small transvections detect every g ≠ 1 without u-coefficients.
- GL_d(F_2) = PSL_d(F_2), so there is no scalar case.

Over F_q, q > 2:
- A nonconstant c ∈ LC(X,F_q)^× commutes with all e_ij(e_V), so h must also allow e_V u (tower indices (0,−1)).
- k can be a scalar matrix in the copy. This is the scalar case of the on-main route, step 5.

The proof then gets longer, which is a reason to keep F_2 in the theorem.
