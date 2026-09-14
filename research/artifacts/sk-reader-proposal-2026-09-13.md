# sk-reader: a strong graduate student reads revision 1

Lane `sk-reader`, 2026-09-13. The text read is `sk/drafts/rev1.tex` (revision 1, landing on main). All line numbers refer to it.
Method: I read every sentence as a strong graduate student who knows crossed products, subshifts and elementary matrices, but not this paper, and redid every step with paper and pencil. I logged each stall, each undefined symbol, and each step that took over a minute.
Status: no ERROR found and no new mathematics; this is a proposal only, with no Cairn nodes. P1 relies on the unreviewed node `brown-mcduff-witness-for-simple-kazhdan-lef-group` (sk-operator-algebras, b01d8ea1f5).

## 0. Stall log (line, what stops the reader, estimated pencil time, fix)

| Line | Stall | Time | Fix |
|---|---|---|---|
| 41 | "answers all three forms": nothing explains why hyperlinear gives Brown's McDuff-factor form | cannot be filled from the paper | P1 |
| 84–85 | The product rule of R is never displayed. The reader rebuilds $(fu^i)(f'u^j)=f(f'\circ T^{-i})u^{i+j}$ from $ufu^{-1}=f\circ T^{-1}$, and it is used at l.125, l.169 and l.198 | 1 min | P2 |
| 114–117 | Why $y_\ell$ has exactly the words of X: the reader has to see that $y_\ell$ agrees with $x$ on $[0,m_\ell+2\ell)$ and that windows start in $[0,m_\ell)$ | 2 min | P3 |
| 174–176 | "lie in $\psi(M_d(\F_2))$ … so $k\in H$". It is unstated that the image is $M_3(\operatorname{span}\epsilon_{ab})$ and closed under products, and why $I_d+A$ is invertible (the role of $k^{-1}-I_3$) | 2 min | P4 |
| 210–215 | The Sturmian computations: which arc gives letter 1, and why the count of ones is $\lfloor\theta+n\alpha\rfloor$ | 3 min | P7 |
| 155–156 | "Since the sets $T^aV$ are disjoint": the reader must compute the product and see that $|a-b+a'|$ can reach $3w$, handled by $V\cap T^jV=\varnothing$ for $|j|\le2w$. Also $V\ne\varnothing$ is needed for $\psi$ to be injective | 1–2 min | P5 |
| 197–200 | How can a word be multiplied out without knowing $L(X)$? The tables are computed in the full-shift algebra | 1 min | P6 |
| 215–217 | Why the continued fraction has the degree of S | 2 min | P8 |
| 69 | "and $G_X$ is not" residually finite: the reason is not given | 10 s | P9 |
| 99–100 | The generator 1 was dropped, so $e_{ij}(1)$ needs $1=\sum_ae_a$ | 20 s | P10 |
| 124 | $\varphi_\ell$ is defined only on elements whose coefficients have window radius at most $\ell$ | 30 s | P11 |
| 128–129 | "the terms with $|j|<m_\ell/2$": for large $\ell$ every exponent qualifies, but the wording suggests only some terms are counted | 30 s | P11 |
| 150–151 | $x$ was fixed in the finite-models section and is reused here as an arbitrary point | 10 s | P12 |
| 39 | "in 2003" against the 2004 bibitem (arXiv against journal) | 10 s | none: lineage decision (RULES §6) |

Undefined but standard, no fix proposed: $\delta_t$, the matrix units $E_{(p,a),(q,b)}$, "transvection between $x$ and $y$" ($=I_d+E_{xy}$), $\chi_S$, $[0;a_1,a_2,\dots]$, sofic and hyperlinear (cited).

Checked and read without a stall:
- l.87–89 ring generators;
- l.100–104 (T) and infiniteness;
- l.120–127 model identities, once P2 is in;
- l.137–144 small sets;
- l.146–152 the h-step;
- l.157–164 $\psi$ and transvection generation;
- l.166–173 the product identity;
- l.176–178 simplicity of $\GL_d(\F_2)$;
- l.180–186 level ideal and covering;
- l.201–203 cylinder words;
- the corollary's invariance and continuum count.

## Tier 1: recommended (+11 lines)

### P1 (l.41): Brown's form
(a) Current l.41:
```latex
The following construction answers all three forms positively.
```
Replacement:
```latex
The following construction answers all three forms positively. For
Brown's form, let $G$ be an infinite simple hyperlinear group. It is
ICC, so $L(G)$ is a $\mathrm{II}_1$ factor, and
$L(G)\subseteq\mathcal R^\omega$~\cite[Proposition~7.1]{Ozawa}. So $G$
lies in the unitary group of the McDuff factor $L(G)\bar\otimes\mathcal R$,
which also embeds in $\mathcal R^\omega$.
```
(c) +5 lines. (d) The paper claims to answer Brown's printed question, and without this bridge the reader cannot check that claim from the paper. It uses $\mathcal R$ for the hyperfinite factor, since $R$ already names the ring. (e) Same content as main's decision 17 (sk-operator-algebras Option A), which waits on a referee-2 PASS.

### P2 (l.84–85): the product rule
(a) Current:
```latex
So every element of $R$ is uniquely a finite sum $\sum_jf_ju^j$, and
$ue_Uu^{-1}=e_{TU}$.
```
Replacement:
```latex
So every element of $R$ is uniquely a finite sum $\sum_jf_ju^j$, the
product is $(fu^i)(f'u^j)=f\,(f'\circ T^{-i})\,u^{i+j}$, and
$ue_Uu^{-1}=e_{TU}$.
```
(c) +1 line. (d) Three later computations (l.125, l.169, l.198) use this rule, and the reader no longer has to derive it.

### P3 (l.114–117): why the periodic word has the right words
(a) Current:
```latex
occurring in $x_{[0,m_\ell+2\ell)}$. This word begins and ends with
$x_{[0,2\ell)}$, so it has period $m_\ell$, and the $m_\ell$-periodic
sequence $y_\ell$ that agrees with $x$ on $[0,m_\ell)$ has the same words
of length $2\ell+1$ as $X$. So $m_\ell$ is at least the number of these
```
Replacement:
```latex
occurring in $x_{[0,m_\ell+2\ell)}$. This word begins and ends with
$x_{[0,2\ell)}$, so the $m_\ell$-periodic sequence $y_\ell$ that agrees
with $x$ on $[0,m_\ell)$ agrees with $x$ on $[0,m_\ell+2\ell)$. Every
window of length $2\ell+1$ of $y_\ell$ is a shift by a multiple of
$m_\ell$ of a window starting in $[0,m_\ell)$, so it is a word of $X$,
and every word of $X$ of this length starts at some position in
$[0,m_\ell)$. So $y_\ell$ has the same words of length $2\ell+1$ as $X$,
and $m_\ell$ is at least the number of these
```
(c) +2 lines. (d) It states the one fact that makes "no new word at the join" checkable. l.118 is unchanged.

### P4 (l.174–176): why $k\in H$
(a) Current:
```latex
$h^{-1}=h=I_3+\epsilon_{00}E_{ij}$. So $k-I_3=(ghg^{-1}-h)h$ and
$k^{-1}-I_3=h(ghg^{-1}-h)$ lie in $\psi(M_d(\F_2))$. As $\psi$ is
injective and multiplicative, $k\in H$. Then $N\cap H$ is a nontrivial
```
Replacement:
```latex
$h^{-1}=h=I_3+\epsilon_{00}E_{ij}$. The image $\psi(M_d(\F_2))$ is the
set of matrices with entries in the span of the $\epsilon_{ab}$, and it
is closed under products. So $k-I_3=(ghg^{-1}-h)h$ and
$k^{-1}-I_3=h(ghg^{-1}-h)$ lie in it, say $k=I_3+\psi(A)$ and
$k^{-1}=I_3+\psi(B)$. As $\psi$ is injective and multiplicative,
$(I_d+A)(I_d+B)=I_d$, so $k$ is the image of $I_d+A$ and $k\in H$.
Then $N\cap H$ is a nontrivial
```
(c) +3 lines. (d) It shows why both $k-I_3$ and $k^{-1}-I_3$ were computed, and turns the membership into a two-line check.

### P7 (l.210–215): the Sturmian checks
(a) Current:
```latex
$\theta+t\alpha\bmod1\ge1-\alpha$~\cite{MorseHedlund}. Its words of
length $n$ are the constant values of $c(\theta)_{[0,n)}$ on the arcs
between the points $-j\alpha\bmod1$, $0\le j\le n$, so $\alpha$ computes
$L(X_\alpha)$. The word $c(\theta)_{[0,n)}$ has
$\lfloor\theta+n\alpha\rfloor$ ones, within $1$ of $n\alpha$, so
$L(X_\alpha)$ computes $\alpha$. Every set $S\subseteq\mathbb N$ has the
```
Replacement:
```latex
$\theta+t\alpha\bmod1\ge1-\alpha$~\cite{MorseHedlund}. So $c(\theta)_t=1$
if and only if $\theta$ lies in the arc $[-(t+1)\alpha,-t\alpha)$ modulo
$1$, and the words of length $n$ of $X_\alpha$ are the constant values of
$c(\theta)_{[0,n)}$ on the arcs between the points $-j\alpha\bmod1$,
$0\le j\le n$. So $\alpha$ computes $L(X_\alpha)$. Since
$c(\theta)_t=\lfloor\theta+(t+1)\alpha\rfloor-\lfloor\theta+t\alpha\rfloor$,
the word $c(\theta)_{[0,n)}$ has $\lfloor\theta+n\alpha\rfloor$ ones,
within $1$ of $n\alpha$, so $L(X_\alpha)$ computes $\alpha$. Every set
$S\subseteq\mathbb N$ has the
```
(c) +2 lines. (d) Both computability claims become one-line checks.
- Check 1: $\{\theta+t\alpha\}\ge1-\alpha$ exactly when $\theta\in[1-\alpha-t\alpha,1-t\alpha)=[-(t+1)\alpha,-t\alpha)$ mod 1.
- Check 2: the floor difference is 1 exactly when $\{\theta+t\alpha\}+\alpha\ge1$, and the sum telescopes to $\lfloor\theta+n\alpha\rfloor-\lfloor\theta\rfloor$ with $\theta\in[0,1)$.

## Tier 2: optional quick wins (+4 lines)

### P5 (l.155–156): the matrix-unit relation
Current:
```latex
$\epsilon_{ab}=e_{T^aV}u^{a-b}$. Since the sets $T^aV$ are disjoint,
$\epsilon_{ab}\epsilon_{a'b'}=\delta_{ba'}\epsilon_{ab'}$. Index the
```
Replacement:
```latex
$\epsilon_{ab}=e_{T^aV}u^{a-b}$. They are nonzero, as $h\ne I_3$ gives
$V\ne\varnothing$. Since
$\epsilon_{ab}\epsilon_{a'b'}=e_{T^aV\cap T^{a-b+a'}V}\,u^{a-b+a'-b'}$ and
$V\cap T^jV=\varnothing$ for $0<|j|\le2w$, we get
$\epsilon_{ab}\epsilon_{a'b'}=\delta_{ba'}\epsilon_{ab'}$. Index the
```
+2 lines. It covers the case $|a-b+a'|>w$ and gives the nonzero condition that injectivity of $\psi$ needs.

### P6 (l.197–200): where the multiplication happens
Current:
```latex
Multiplying out a word in the generators gives a matrix with entries
$\sum_jf_ju^j$, each $f_j$ a table on words, using $uf=(f\circ T^{-1})u$.
The word is trivial if and only if the tables of its difference from
```
Replacement:
```latex
Multiplying out a word in the generators in $\LC(A^{\Z},\F_2)\rtimes\Z$,
which maps onto $R$, gives a matrix with entries $\sum_jf_ju^j$, each
$f_j$ a table on words, using $uf=(f\circ T^{-1})u$. The word is trivial
in $G_X$ if and only if the tables of its difference from
```
+1 line. The algorithm visibly needs $L(X)$ only for the final test.

### P8 (l.215–217): the continued fraction
Current:
```latex
$L(X_\alpha)$ computes $\alpha$. Every set $S\subseteq\mathbb N$ has the
degree of the irrational number $[0;1+\chi_S(0),1+\chi_S(1),\dots]$, and
the degree of the word problem is an isomorphism invariant.
```
Replacement, the last two lines:
```latex
degree of the irrational number $[0;1+\chi_S(0),1+\chi_S(1),\dots]$, since
each digit is decided by one strict comparison of this number with a
rational computed from the earlier digits. The degree of the word problem
is an isomorphism invariant.
```
+1 line. The strict comparison with $[0;a_1,\dots,a_k,2]$ decides $a_{k+1}\in\{1,2\}$ because the number is irrational, and the convergents give the other direction.

### P9 (l.69): not residually finite
Current: `and $G_X$ is not, so $G_X$ is not finitely presented. We do not know`
Replacement: `and the infinite simple group $G_X$ is not, so $G_X$ is not finitely presented. We do not know`
+0 lines.

### P10 (l.99–100): the dropped generator 1
Current: `generate $G$. By Ershov and Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ},`
Replacement: `generate $G$, as $1=\sum_ae_a$. By Ershov and Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ},`
+0 lines.

### P11 (l.124, l.128–129): the domain of $\varphi_\ell$
- l.124. Current: `and put $\varphi_\ell(\sum_jf_ju^j)=\sum_jD_\ell(f_j)P^j$. Since`
  Replacement: `and, when every $f_j$ depends only on coordinates in $[-\ell,\ell]$, put $\varphi_\ell(\sum_jf_ju^j)=\sum_jD_\ell(f_j)P^j$. Since`
- l.129. Current: `terms with $|j|<m_\ell/2$ have disjoint supports, so $\varphi_\ell(r)\ne0$.`
  Replacement: `terms $D_\ell(f_j)P^j$ have disjoint supports once $m_\ell>2|j|$ for all exponents $j$ of $r$, so $\varphi_\ell(r)\ne0$.`
+1 line.

### P12 (l.150–151): the reused letter $x$
Current: `vanishes for every clopen $V$. Choosing $V$ to contain $x$ but not` / `$T^{-j}x$, we get $c_j(x)=0$ for $j\ne0$. So $c\in\LC(X,\F_2)$, and`
Replacement: `vanishes for every clopen $V$. Choosing $V$ to contain $z$ but not` / `$T^{-j}z$, we get $c_j(z)=0$ for all $z\in X$ and $j\ne0$. So $c\in\LC(X,\F_2)$, and`
+0 lines.

## Summary
- Tier 1 (P1–P4, P7) costs +13 lines. Without P1 it is +8 lines, if main keeps Brown's bridge for decision 17's text instead.
- Tier 2 costs +4 lines.
- No claim changes, no new machinery, and no new unverified fact except P1's operator-algebra import (Ozawa Prop 7.1; the witness node is unreviewed).
- The longest remaining pencil steps after these fixes are l.125–127 (model multiplicativity, about 1 min) and l.166–173 (about 1 min). Both are routine given P2.
