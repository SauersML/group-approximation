# sk-proof-minimal-concrete proposal, part 1: change table, length, trade-off, checks

- Lane: sk-proof-minimal-concrete (SK swarm, 2026-09-13).
- Base: frozen note `manuscript-disk-1646.tex`, md5 7b3dc4ec92b4581553bc0dc2b0edcb99. This is the untracked 340-line `simple_kazhdan_sofic_group.tex`.
- Replaced range: lines 67–227, from `\section{Proof of Theorem~\ref{thm:main}}` to `Thus $N=G$, completing the proof.\hfill$\square$`.
- Candidate: part 2 of this proposal.
- Status: UNREVIEWED; queued with sk-referee-1. No Cairn node changes. The rewrite proves the F_2 case of the established `simple-kazhdan-lef-group-from-minimal-subshift`, so it adds no new claim.

## (a) What changes (before quoted verbatim from the frozen copy; after from part 2)

1. **Simplicity of R is no longer used.**
   - Before (l.102–109): "We will also need that $R$ is simple and $Z(R)=\F_2$. These are standard groupoid-algebra facts~\cite{BCFS,ClarkEdie,Steinberg}; here is the direct argument. A nonzero two-sided ideal contains an element $r=\sum_j f_ju^j$ with $f_0\ne0$, after multiplication by a power of $u$. Choose a nonempty clopen $U$ on which $f_0=1$, disjoint from $T^jU$ for every nonzero exponent occurring in $r$. Then $e_Ure_U=e_U$. Finitely many translates of $U$ cover $X$, so the ideal contains $1=1-\prod_i(1-e_{T^{n_i}U})$."
   - After: "The center of $R$ is $\F_2$~\cite{BCFS,ClarkEdie,Steinberg}. Indeed, ..." The final step shows directly that the ideal $I_N\ni e_W$ contains 1 (translates of $W$ cover $X$).
   - The ideal-reduction argument disappears. sk-citations should confirm which of the three references covers the center over $\F_2$; they were cited for simplicity and center together.
2. **No separate Z(G) paragraph.**
   - Before (l.114–116): "Finally, commuting with every $e_{ij}(1)$ forces a central element of $G$ to be $cI_3$; commuting with all $e_{ij}(r)$ gives $c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$."
   - After: the same deduction runs once, inside the step that finds $h$: "Otherwise $g$ commutes with every $e_{ij}(1)=\prod_Ce_{ij}(e_C)$, so $g=cI_3$ with $c\in R$. Then $c$ commutes with every $e_C$ and $e_Cu$, hence with $u^{\pm1}$ and every $e_a$. So $c\in Z(R)^\times=\{1\}$, a contradiction."
3. **Two kinds of $s$, no translates.**
   - Before (l.182–184 and l.189–193): "$s\in\{e_C,e_Cu,e_Cu^{-1}:C\in\mathcal P\}$" and "Each such $s$ lies in $B_1(U)$ for a translate $U$ of $C$: $e_C=E_{00}(C),\quad e_Cu=E_{10}(T^{-1}C),\quad e_Cu^{-1}=E_{-1,0}(TC)$."
   - After: "$s\in\{e_C,e_Cu:C\in\mathcal P\}$" and "$s=E_{00}(C)$ or $s=E_{0,-1}(C)$ lies in $B_1(C)$". Commuting with $u$ gives commuting with $u^{-1}$.
4. **Tower height.** Before (l.180): "$0<|j|\le2w+3$". After: "$0<|j|\le2m$" with $m=w+1$. That is $2w+2$, exactly what $B_m(C)$ needs.
5. **Towers under one fixed hypothesis.**
   - Before (l.155): "Suppose the levels $T^aU$ are disjoint for all indices needed below." (l.166–171): "If $r,r'$ involve only powers $u^j$ with $|j|\le w$, then $rB_m(U)r'\subseteq B_{m+w}(U)$, provided the larger tower is disjoint."
   - After: "Let $C\subseteq X$ be clopen with $C\cap T^jC=\varnothing$ for $0<|j|\le2m$." and "$rB_{m-w}(C)\,r'\subseteq B_m(C)$."
6. **The commutator is displayed; no corner unit.**
   - Before (l.195–201): "By~\eqref{eq:absorb}, both $k-I_3$ and $k^{-1}-I_3$ lie in $M_3(B_m(U))$. If $e$ is the unit of $B_m(U)$, then $k=(1-e)I_3+ek e$. Its corner part is invertible and therefore corresponds to a locally constant function $\kappa:U\longrightarrow\GL_d(\F_2),\qquad d=3(2m+1)\ge9.$"
   - After: "$k-I_3=(gSg^{-1}-S)(I_3+S),\qquad k^{-1}-I_3=(I_3+S)(gSg^{-1}-S)$", plus, in the tower paragraph: "The $k\in\GL_3(R)$ such that $k-I_3$ and $k^{-1}-I_3$ lie in $M_3(B_m(C))$ form a group, and $k\mapsto I_d+(k-I_3)$ identifies it with $\LC(C,\GL_d(\F_2))$."
   - "Conjugation by $k$ acts on $H_W$ as conjugation by $\kappa_0$" is then pointwise conjugation.
7. **$H_W\subseteq G$ through the Steinberg relation in $\GL_d(\F_2)$.**
   - Before (l.209–215): "For $p=q$ and $a\ne b$, take $q\ne p$ and use $[e_{pq}(E_{ab}(W)),e_{qp}(E_{bb}(W))] =I_3+E_{ab}(W)E_{pp}.$ This follows from $E_{ab}E_{bb}=E_{ab}$ and $E_{bb}E_{ab}=0$. These transvections generate $H_W$."
   - After: "The transvections $I_d+E_{xy}$ generate $\GL_d(\F_2)$. ... For $p\ne q$ the transvection of $H_W$ between $(p,a)$ and $(q,b)$ is $e_{pq}(E_{ab}(W))$, and the others are commutators of these, by $[I_d+E_{xy},I_d+E_{yz}]=I_d+E_{xz}$."
8. **Level ideal without permutation matrices or simplicity of R.**
   - Before (l.223–227): "Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal: permutation matrices in $G$ move any elementary position to any other, and~\eqref{eq:elementary} gives addition and multiplication on either side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is simple, $I_N=R$."
   - After: "Finally, $I_N=\{r\in R:e_{ij}(r)\in N\text{ for all }i\ne j\}$ is a two-sided ideal by~\eqref{eq:elementary}, and it contains $e_W$. So it contains every $e_{T^nW}=u^ne_Wu^{-n}$. By minimality and compactness finitely many of these sets cover $X$, so $1=1-\prod_i(1-e_{T^{n_i}W})\in I_N$."
9. **Notation clashes removed.** In "Finite models" the window parameter $k$ and the period $N$ (l.123–149) become $\ell$ and $L$. Later $k=[g,h]$ and $N\trianglelefteq G$.
10. **Periodic-word lemma stated so the join is visibly harmless.**
    - Before (l.126–128): "choose two occurrences of the same word of length $2k$, separated by a segment $w$ long enough to contain every word of length $2k+1$". Here "separated by" can be read as the gap strictly between the occurrences, and repeating that gap does create new words.
    - After: "Let $w$ be the word of length $L$ that begins at the first occurrence. Then $wv$ occurs in $X$ and $w$ contains every word of $X$ of length $2\ell+1$".
11. **Small compressions.**
    - Generators: "$s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$" becomes "$s\in\{u,u^{-1}\}\cup\{e_a:a\in A\}$, because $\sum_ae_a=1$".
    - No periodic points: the sentence (l.78–82) moves to where the partition is chosen.
    - l.150–152 ("The regular permutation actions ... hyperlinear models \cite{Pestov}.") becomes "So $G$ is LEF, hence sofic and hyperlinear~\cite{Pestov}."

## (c) Length
- Lines 67–227: 161 source lines. Part 2: 119 source lines, so Δ = −42 lines (−26%).
- Full note: 340 → 298 lines.
- MSI pdflatex (texlive 2025, 3 passes, `/scratch.global/sauer354/sk/sk-proof-minimal-concrete/{cur,cand}`): both notes give 0 errors, 0 overfull boxes, 0 undefined references, 4 pages.

## (d) Reader-facing trade-off
Same theorem and same rigor, in 42 fewer lines. The reader no longer checks the simplicity of R, permutation matrices, a special same-row commutator, translated towers or corner units, and nothing new must be trusted.

## (e) Line-by-line verification notes (my own checks; independent review pending)
1. $[e_{ik}(r),e_{kj}(s)]=e_{ij}(rs)$: expand $(I+rE_{ik})(I+sE_{kj})(I-rE_{ik})(I-sE_{kj})$ using $E_{kj}E_{ik}=E_{ij}E_{ik}=E_{ij}E_{kj}=0$ for distinct $i,j,k$.
2. $u^{-t}e_au^t=e_{T^{-t}\{x_0=a\}}=e_{\{x_t=a\}}$, since $ue_Uu^{-1}=e_{TU}$ and $(T^tx)_0=x_t$.
3. Periodic word.
   - Let $w=x_{[p,p+L)}$ with $x_{[p,p+2\ell)}=x_{[p+L,p+L+2\ell)}=v$.
   - A window of $y$ of length $2\ell+1$ that starts inside one copy of $w$ lies inside $w$ followed by the first $2\ell$ letters of $w$, i.e. inside $wv$, which is a word of $X$.
   - If $L$ exceeds the uniform recurrence bound for words of length $2\ell+1$, then $w$ contains all of them. Occurrences of $v$ recur, so $L$ can be taken arbitrarily large.
4. $P^iD(f)P^{-i}\delta_n=f(y_{n-i-\rho}\cdots y_{n-i+\rho})\delta_n$.
   - Since $(T^{-i}x)_t=x_{t-i}$, this is the $n$-th entry of $D(f\circ T^{-i})$, whose window is $\rho+|i|\le\ell$.
   - So $D(f)P^iD(g)P^j=D(f\cdot g\circ T^{-i})P^{i+j}$, the image of $(fu^i)(gu^j)=f(g\circ T^{-i})u^{i+j}$.
5. Injectivity.
   - For exponents $|j|<L/2$ the $P^j$ are permutation matrices with disjoint supports. So $\sum_jD(f_j)P^j=0$ forces every $D(f_j)=0$, and then $f_j=0$, because every word of length $2\ell+1$ of $X$ occurs in $y$.
   - The images of group elements are invertible, because the products $gg^{-1}$ are among the controlled products.
6. Matrix units.
   - $E_{ab}(W)E_{cd}(W')=e_{T^aW}e_{T^{a-b+c}W'}u^{a-b+c-d}$. If $b\ne c$, these sets lie in $T^aC$ and $T^a(T^{c-b}C)$, which are disjoint because $0<|c-b|\le2m$.
   - Independence: for a fixed exponent $a-b$, distinct $a$ give disjoint levels $T^aC$.
7. Absorption.
   - $fu^i\cdot e_{T^aW}u^{a-b}\cdot f'u^j=e_{T^{a+i}W'}u^{(a+i)-(b-j)}$, where $T^{a+i}W'=T^{a+i}W\cap\{f=1\}\cap\{f'\circ T^{-(a+i-b)}=1\}$.
   - With $|a|,|b|\le m-w$ and $|i|,|j|\le w$ the indices stay within $m$.
8. The commutator formulas.
   - Over $\F_2$, $h^{-1}=h=I_3+S$, and $S^2=0$ since $i\ne j$.
   - $k=(ghg^{-1})h$, so $k-I_3=(ghg^{-1}-h)h=(gSg^{-1}-S)(I_3+S)$.
   - $k^{-1}=h\,(ghg^{-1})$, so $k^{-1}-I_3=h(ghg^{-1}-h)=(I_3+S)(gSg^{-1}-S)$.
   - The entries of $gSg^{-1}$ are $g_{pi}\,s\,(g^{-1})_{jq}\in rB_1(C)r'\subseteq B_{w+1}(C)$.
9. $e_C=E_{00}(C)$, and $e_Cu=e_{T^0C}u^{0-(-1)}=E_{0,-1}(C)$.
10. The group $\{k:k^{\pm1}-I_3\in M_3(B_m(C))\}$.
    - It is closed under products, since $(I+X)(I+X')=I+(X+X'+XX')$.
    - $k\mapsto I_d+\Phi(k-I_3)$ is multiplicative because $\Phi:M_3(B_m(C))\to\LC(C,M_d(\F_2))$ is a ring isomorphism.
    - The inverse sends $\kappa$ to $I_3+\Phi^{-1}(\kappa-I_d)$.
11. The transvection $I_d+1_WE_{(p,a),(q,b)}$ corresponds to $I_3+E_{ab}(W)E_{pq}=e_{pq}(E_{ab}(W))$ when $p\ne q$. For $x=(p,a)$ and $z=(p,b)$ with $a\ne b$, take $y=(q,0)$ with $q\ne p$: then $[I+E_{xy},I+E_{yz}]=I+E_{xz}$.
12. Conjugation is pointwise. $\kappa\varphi\kappa^{-1}$ for $\varphi\in H_W$ is $I_d$ off $W$ and $\kappa_0Z\kappa_0^{-1}$ on $W$.
13. $[k,x]=(kxk^{-1})x^{-1}\in H_W\cap N$. Some $x$ gives $[k,x]\ne1$, because $\kappa_0\ne I_d$ and $\GL_d(\F_2)$ is centerless.
14. The level ideal.
    - Additivity comes from the first identity. $e_{ij}(sr)=[e_{ik}(s),e_{kj}(r)]$ and $e_{ij}(rs)=[e_{ik}(r),e_{kj}(s)]$ lie in the normal subgroup $N$.
    - $e_{ij}(e_W)=I_3+E_{00}(W)E_{ij}\in H_W$.
    - The translates $T^nW$ form an open cover (minimality), so finitely many suffice.
15. The scalar step.
    - $g$ commutes with $I_3+E_{ij}$ for all $i\ne j$, so $g$ is scalar.
    - $cI_3$ commuting with $e_{12}(e_C)$ and $e_{12}(e_Cu)$ gives $ce_C=e_Cc$ and $c\,e_Cu=e_Cu\,c$.
    - Summing over $C$ gives $cu=uc$, so $cu^{-1}=u^{-1}c$. Also $e_a=\sum_{C\subseteq\{x_0=a\}}e_C$.
16. The center.
    - $ce_V-e_Vc=\sum_jf_j(e_{T^jV}-e_V)u^j$. At $x\in V$ with $T^{-j}x\notin V$, the coefficient of $u^j$ is $f_j(x)$.
    - $cu=uc$ gives $f_0=f_0\circ T^{-1}$, so $\{f_0=1\}$ is a clopen invariant set, hence $\varnothing$ or $X$.
17. The only tower used is $B_m(C)$ with $m=w+1$. Its levels are disjoint iff $C\cap T^jC=\varnothing$ for $0<|j|\le2m$.

## Considered and not adopted (reader merits)
- Replacing the direct center argument by the citation alone saves 4 lines, but the reader would have to trust a groupoid-algebra citation over $\F_2$ for a four-line fact.
- The ultraproduct formulation of LEF: sk-lef-short owns this. At this level of detail it is not shorter than the partial-model paragraph.
- Citing a Bass–Vaserstein sandwich theorem in place of the tower argument: sk-stable-rank-a/b own this. It depends on the stable rank of R, which is not known here.

## Notes for the referees on the current text (no ERROR found)
- UNCLEAR, l.126–128: "separated by a segment $w$" can be read as the gap between the two occurrences, and repeating the gap creates new words. Item 10 above fixes this.
- UNCLEAR, l.155: "for all indices needed below" leaves the height implicit. Items 4 and 5 fix this.
- Notation: $k$ and $N$ each have two meanings in the current proof. Item 9 fixes this.
- Nothing false was found in l.67–227. The tower height $2w+3$ is more than needed, which is harmless.
