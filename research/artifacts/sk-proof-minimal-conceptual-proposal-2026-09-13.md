# sk-proof-minimal-conceptual: the proof as two ring lemmas (proposal, part 1 of 2)

Lane `sk-proof-minimal-conceptual`, SK swarm, 2026-09-13.
- Source: `$SK/manuscript-disk-1646.tex` (340 lines, md5 7b3dc4ec…).
- Candidate full manuscript: `$SK/lanes/sk-proof-minimal-conceptual/skg-conceptual.tex` (314 lines). MSI pdflatex, two passes: 0 errors, 0 overfull boxes, 4 pages; the current disk version also compiles to 4 pages.
- Part 2 quotes the current proof section (disk l.67–227) verbatim.

## Summary
The proof section (disk l.67–227, 161 lines) becomes two lemmas about rings and three short checks for the subshift ring. The candidate's l.65–201 is 137 lines, reproduced below.

- **Lemma 1 (LEF).** If R is a unital subring of an algebraic ultraproduct of finite rings, then GL_n(R) is LEF.
- **Lemma 2 (simplicity).** Let R be a simple ring such that, for every finite F ∋ 1, the elements s with tFs = 0 for some t ≠ 0 generate R. Then every normal subgroup of EL_n(R), n ≥ 3, is central or everything.
  - This is the criterion `local-annihilation-makes-projective-el-simple`, already established on main.
  - The proof written here is a self-contained two-commutator extraction:
    - γ = [g, e_ij(s)] satisfies t(γ − I) = 0;
    - η = [γ, e_pl(at)] = I + (γ − I)atE_pl is supported in one column;
    - [η, e_dm(1)] = e_dl(c) with c ≠ 0.
- **The subshift ring satisfies Lemma 2** by a 10-line clopen argument: t = e_W, s = e_V r, with W missing the orbit segment of x and V a small neighborhood of x. This replaces:
  - the tower algebras B_m(U) and the absorption (eq:absorb);
  - the partition with C ∩ T^jC = ∅;
  - the copy of GL_d(F_2), d ≥ 9, over a tower, and its transvection generation;
  - the simplicity of GL_d(F_2).
- **Finite models:** the same periodic words, assembled into an injective unital ring homomorphism R → ∏_ω M_{N_k}(F_2); Lemma 1 then gives LEF. This removes the bookkeeping of entries, inverses, differences and intermediate sums (disk l.146–149).

**Length.**
- Proof section: −24 lines.
- Whole note: −26 lines (340 → 314).
- The saving is all in simplicity: disk l.154–227 (74 lines) becomes 47 lines, counting Lemma 2 with its proof and the "Simplicity" subsection.
- LEF is length-neutral: l.118–152 (35 lines) becomes 36 lines, Lemma 1 included.

## (d) Reader-facing trade-off
Shorter, with less machinery: the reader no longer needs tower algebras, absorption, or the simplicity of GL_d(F_2). The only new notion is the algebraic ultraproduct, used in a three-line lemma.

## Verdict on reader merits
- **Adopt the simplicity part** (Lemma 2 plus the "Simplicity" subsection) in place of disk l.154–227. It is strictly shorter and more elementary, and it states a reusable theorem about simple rings.
- **The LEF part is a matter of taste at equal length.**
  - The ultraproduct version has the lemma format and drops the bookkeeping.
  - The current partial-model version needs no ultrafilter.
  - I recommend the candidate as a whole. Mixing the current LEF text with Lemma 2 also works: keep disk l.118–152, delete Lemma 1, and the note is about 36 lines shorter than now minus the 10 lines of Lemma 1.
- Against the concrete rewrite (sk-proof-minimal-concrete), the decisive gain is the simplicity step. Any concrete version that keeps the tower argument inherits l.154–227.

## (e) Status
- **Lemma 2 = `local-annihilation-makes-projective-el-simple`.** ESTABLISHED on main: Lean `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`; the criterion was reviewed PASS by un-verify.
  - The explicit extraction text above is new and UNREVIEWED; queued with sk-referee-1.
  - Credit: un-stepanov-credit attributes the extraction mechanism to Stepanov's Lemma 4.3 (J. Math. Sci. 95 (1999) p. 2151). The lemma number is still to be checked by sk-citations.
- **The hypothesis for the subshift ring** is Theorem S1 of `research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md` (Lean `localAnnihilation_of_crossedProduct`); the version here is specialized to T.
- **The ultraproduct embedding** is item 3 of `minimal-subshift-algebra-is-simple-lef-ring`.
- No new Cairn claim: every mathematical statement in the candidate is already a node on main.

## (a)+(b) The edits, verbatim

### E1. Preamble (disk l.8–16)
Before (l.8–9 and l.15–16):
```latex
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}[theorem]{Corollary}
\newcommand{\SL}{\operatorname{SL}}
\newcommand{\PSL}{\operatorname{PSL}}
```
After (the `\SL` and `\PSL` macros are unused in the candidate):
```latex
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
```

### E2. Abstract (disk l.32–34)
Before:
```latex
Brown, Ozawa, and Pestov. The proof combines periodic approximation
with a commutator supported on a finite tower. Every Turing degree
occurs as the word-problem degree of one of these groups.
```
After:
```latex
Brown, Ozawa, and Pestov. The proof combines periodic approximation
with an elementary-matrix extraction for normal subgroups. Every Turing
degree occurs as the word-problem degree of one of these groups.
```

### E3. Introduction (disk l.58–62)
Before:
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
a nontrivial normal subgroup meets a finite simple matrix group
supported on a clopen tower, and therefore contains an elementary
matrix. This is an explicit elementary-matrix extraction argument,
in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
```
After:
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is simplicity: using left
annihilators in the ring, one extracts an elementary matrix from any
noncentral normal subgroup (Lemma~\ref{lem:simple}), following
Stepanov~\cite[Lemma~4.3]{Stepanov}.
```

### E4. Proof section: disk l.67–227 (quoted in part 2) replaced by
```latex
\section{Proof of Theorem~\ref{thm:main}}

\subsection*{Elementary groups}
For a unital ring $R$, $n\ge3$, $i\ne j$ and $r\in R$, put
$e_{ij}(r)=I_n+rE_{ij}$, where $E_{ij}$ is the matrix unit. These
matrices generate $\EL_n(R)$. With $[g,h]=ghg^{-1}h^{-1}$ they satisfy
\begin{equation}\label{eq:elementary}
 \begin{aligned}
 e_{ij}(r+s)&=e_{ij}(r)e_{ij}(s),\qquad i\ne j,\\
 [e_{ik}(r),e_{kj}(s)]&=e_{ij}(rs),\qquad i,j,k\text{ distinct}.
 \end{aligned}
\end{equation}
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.

\begin{lemma}\label{lem:lef}
If $R$ is a unital subring of an algebraic ultraproduct $\prod_\omega Q_k$
of finite rings, then $\GL_n(R)$ is LEF.
\end{lemma}

\begin{proof}
$\GL_n(R)$ is a subgroup of $\prod_\omega\GL_n(Q_k)$. Given finitely many
elements, each product relation and each inequality among them holds in
$\GL_n(Q_k)$ for $\omega$-almost every $k$, so a single $k$ realizes all
of them.
\end{proof}

\begin{lemma}\label{lem:simple}
Let $R$ be a simple ring such that, for every finite set $F\subseteq R$
containing $1$, the elements $s$ with $tFs=0$ for some nonzero $t\in R$
generate $R$ as a ring. Then every normal subgroup of $\EL_n(R)$,
$n\ge3$, is central or all of $\EL_n(R)$.
\end{lemma}

\begin{proof}
Let $N$ be a normal subgroup of $G=\EL_n(R)$, and let $g\in N$ be
noncentral. Let $F$ consist of $1$ and the entries of $g$.
By~\eqref{eq:elementary}, the coefficients $r$ such that $g$ commutes with
every $e_{ij}(r)$ form a subring, which is proper because $g$ is
noncentral. So there are $s\in R$ and $t\ne0$ with $tFs=0$, and a matrix
$h=e_{ij}(s)$ with $\gamma=[g,h]\ne I_n$. Every entry of $ghg^{-1}-h$ is a
sum of products $fsf'$ with $f\in F$, so
$t(\gamma-I_n)=t(ghg^{-1}-h)h^{-1}=0$. Thus $t\gamma=tI_n$, and so
$t\gamma^{-1}=tI_n$.

Choose a nonzero entry $b=(\gamma-I_n)_{qp}$. Since $RtR=R$, some $a\in R$
gives $bat\ne0$. Take $l\ne p$. As $atE_{pl}\gamma^{-1}=atE_{pl}$ and
$(atE_{pl})^2=0$,
\[
 \eta=[\gamma,e_{pl}(at)]=(I_n+\gamma\,atE_{pl})(I_n-atE_{pl})
 =I_n+(\gamma-I_n)\,atE_{pl}
\]
lies in $N$, and its $(q,l)$ entry is $bat\ne0$. The matrix $\eta$ fixes
each basis vector $e_d$ with $d\ne l$, and so does $\eta^{-1}$. So
$\eta^{-1}-I_n$ is nonzero only in column $l$. Choose a nonzero entry
$c=(\eta^{-1}-I_n)_{ml}$ and an index $d\notin\{m,l\}$. Then
$\eta E_{dm}=E_{dm}$ and $E_{dm}\eta^{-1}=E_{dm}+cE_{dl}$, so
$[\eta,e_{dm}(1)]=e_{dl}(c)\in N$.

Finally, $I=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal: signed
permutation matrices in $G$ move $e_{12}(r)$ to every $e_{ij}(\pm r)$,
and~\eqref{eq:elementary} gives sums and products on either side. It
contains $c\ne0$, so $I=R$ and $N=G$.
\end{proof}

\subsection*{The ring and property (T)}
Write $e_U$ for the indicator of a clopen set $U\subseteq X$. Our
conventions are $(Tx)_n=x_{n+1}$ and
\[
 R=\LC(X,\F_2)\rtimes_T\Z
   =\left\{\sum_j f_j u^j:\text{finite sums}\right\},
 \qquad ufu^{-1}=f\circ T^{-1},
\]
where $\LC$ denotes locally constant functions. Thus $u^je_U=e_{T^jU}u^j$.
Minimality and infiniteness imply that $T$ has no periodic points.

The ring $R$ is generated by $u,u^{-1}$ and the letter indicators
$e_a=e_{\{x:x_0=a\}}$: their translates and products give all cylinder
indicators. By~\eqref{eq:elementary}, the matrices $e_{ij}(s)$ with
$s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$ generate $G=\EL_3(R)$.
Ershov--Jaikin-Zapirain's theorem says that $\EL_n(R)$ has property~(T)
for every finitely generated unital associative ring $R$ and
$n\ge3$~\cite[Theorem~1.1]{EJZ}. Hence $G$ has property~(T).
It is infinite because $e_{12}(\LC(X,\F_2))$ is infinite.

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

\subsection*{Simplicity}
Let $F\subseteq R$ be finite, and let $L$ bound the absolute exponents of
$u$ in $F$. For $x\in X$, choose a nonempty clopen $W$ missing the points
$T^jx$ with $|j|\le L$, and then a clopen $V\ni x$ with
$T^jV\cap W=\varnothing$ for $|j|\le L$. Then $e_Wfe_V=0$ for every
$f\in F$, so $t=e_W$ gives $tF(e_Vr)=0$ for every $r\in R$. Finitely many
such $V$ cover $X$, and refining them to a clopen partition
$V_1,\dots,V_p$ gives $r=\sum_ie_{V_i}r$. So Lemma~\ref{lem:simple}
applies, and $G$ is simple because $Z(G)=\{1\}$.

\subsection*{Finite models}
For each $k$, there is a periodic sequence $y_k=w_k^\infty$ with exactly
the same words of length $2k+1$ as $X$. Indeed, minimality implies
uniform recurrence. In a point of $X$, choose two occurrences of the
same word of length $2k$, separated by a segment $w_k$ long enough to
contain every word of length $2k+1$. Repeating this segment introduces
no new word of that length at the join. Its length $N_k$ can be chosen
larger than $k$.

Let $P_k\delta_n=\delta_{n+1}$ on $\F_2^{\Z/N_k\Z}$. If $f$ depends on the
coordinates in $[-\rho,\rho]$ and $\rho\le k$, evaluating its local rule
along $y_k$ gives a diagonal matrix $D_k(f)$. Fix a nonprincipal
ultrafilter $\omega$ on $\mathbb N$ and put
\[
 \varphi\Bigl(\sum_jf_ju^j\Bigr)=\Bigl(\sum_jD_k(f_j)P_k^j\Bigr)_k
 \in\prod_\omega M_{N_k}(\F_2),
\]
where the coordinates with small $k$ are $0$. The relations
$D_k(ff')=D_k(f)D_k(f')$ and $P_kD_k(f)P_k^{-1}=D_k(f\circ T^{-1})$ hold
once $k$ exceeds the windows involved, so $\varphi$ is a unital ring
homomorphism. It is injective: if $f_j\ne0$, a window on which $f_j=1$
occurs in $y_k$, and distinct exponents $|j|<N_k/2$ occupy distinct
cyclic diagonals. By Lemma~\ref{lem:lef}, $G$ is LEF. The regular
permutation actions of the finite groups $\GL_{3N_k}(\F_2)$ give sofic
models; their permutation matrices give hyperlinear
models~\cite{Pestov}.\hfill$\square$
```

The corollary section (disk l.229–262), the credit paragraph and the bibliography are unchanged. `\eqref{eq:elementary}` and "the finite generators above" still resolve.

## Checks for the referee (each identity used)
- **t(γ − I) = 0.** γ − I = (ghg^{-1} − h)h^{-1}, and the (p,q) entry of ghg^{-1} − h is g_{pi} s (g^{-1})_{jq} − δ_{pi}δ_{jq} s. Both terms vanish after left multiplication by t, since t g_{pi} s = 0 and ts = 0 (1 ∈ F).
- **atE_pl γ^{-1} = atE_pl.** Row l of tγ^{-1} is t e_l^T, because tγ = tI gives tγ^{-1} = tI.
- **η = I + (γ − I)atE_pl.** Expand (I + γatE_pl)(I − atE_pl) and use (atE_pl)^2 = 0, since l ≠ p. Its (q,l) entry is bat ≠ 0.
- **η^{-1} − I lives in column l.** η e_d = e_d for d ≠ l, so η^{-1} e_d = e_d as well.
- **[η, e_dm(1)] = e_dl(c).** Using ηE_dm = E_dm and E_dm η^{-1} = E_dm + cE_dl, we get (I + E_dm + cE_dl)(I − E_dm) = I + cE_dl. This uses E_dm E_dm = 0 (d ≠ m) and E_dl E_dm = 0 (l ≠ d). The case m = l is included.
- **Level ideal.** e_dl(c) is conjugate by a signed permutation matrix to e_12(±c), so c ∈ I.
- **Local annihilation for R.** e_W f_j u^j e_V = f_j e_{W ∩ T^jV} u^j = 0 for |j| ≤ L; the case j = 0 gives e_W e_V = 0. X is infinite, so a nonempty clopen W missing the finite set {T^jx : |j| ≤ L} exists; V comes from continuity.
- **φ is a ring homomorphism.** For fixed r, r' ∈ R, the products need P_k^i D_k(f) P_k^{-i} = D_k(f∘T^{-i}) and D_k(ff') = D_k(f)D_k(f') at window radius ≤ k. That holds for all large k, so ω-almost everywhere.
- **φ is injective.** If f_j ≠ 0, a word of X on which f_j = 1 occurs in y_k once k ≥ its radius. Exponents with |j| < N_k/2 are distinct mod N_k, so the terms occupy different cyclic diagonals and cannot cancel.
- **Lemma 1.** M_n(∏_ω Q_k) = ∏_ω M_n(Q_k), and invertibility is coordinatewise ω-almost everywhere.

## Model tests for Lemma 2's hypothesis
- A field fails it: tFs = 0 with t ≠ 0 forces s = 0. So the lemma says nothing about PSL_n(k), as it should.
- LC(X,F_2) with X Cantor satisfies it but is not simple, and EL_n of it has congruence normal subgroups. So simplicity of R is needed.
- The subshift ring satisfies it (the "Simplicity" subsection).
- The simplicity check uses only that X is infinite; minimality enters through the simplicity and centre of R.

## A remark the note could carry (not in the candidate)
The Simplicity subsection works verbatim for every Steinberg algebra of an ample groupoid with infinite compact unit space (Theorem S1 of the un-simplicity artifact). So Lemma 2 gives simple EL_n/Z over every simple such algebra, the Leavitt algebras L_k(1,d) included. Whether to state this is for sk-general-master; it costs one sentence.
