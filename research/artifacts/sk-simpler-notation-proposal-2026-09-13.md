# sk-simpler-notation: notation and readability pass on the note (proposal)

Lane sk-simpler-notation, 2026-09-13.
- Target: main's `simple_kazhdan_sofic_group.tex` at e80dcf20ad (rev2, md5 4ad49212…, 386 lines). Line numbers refer to that blob.
- No rev3 existed when I started. Every before-block is a verbatim quote, so the renames transfer to rev3 by string match.
- Status: proposal only. No mathematics changes, no Cairn nodes, nothing to review except the WLOG step in N5, which is checked below.
- Net length: +3 source lines (N3, N5, N9). Everything else is a rename, or a rewrite at equal length.

## 0. Symbol inventory and clashes found

| symbol | meanings in rev2 | where | fix |
|---|---|---|---|
| N | matrix size in SL_{3N}; least period N_ℓ; the normal subgroup | l.57, 130–161 / l.180–237 | N1 |
| k | third index in (1); the commutator [g,h] | l.106 / l.213–226 | N2 |
| S | the ring in the EJZ statement; a set S ⊆ ℕ; the shift of Y | l.111–113 / l.272 / l.289 | N3 |
| A | the alphabet; a matrix in M_d(F_2) | l.49, 109, 147, 252 / l.207, 224–226 | N4 |
| i, j | matrix indices of h; exponents of u (same paragraph) | l.189, 220–221 / l.182–183, 192–194 | N5 |
| L | length of a word; the language L(X); the algebra L(G) (adjacent paragraphs) | l.157–158 / l.242–271 / l.168–171 | N6 |
| n | rank of EL_n; word length in §2 | l.60, 83, 111 / l.258–271 | N7 |
| G, G_X | two names for the same group | l.99–237 / abstract, theorem, §2 | N8 |
| t | index of δ_t; generators t_±, t_a of the free algebra (adjacent paragraphs) | l.134–137 / l.147–150 | N10 |

Structure:
- the operator-algebra paragraph uses simplicity one subsection before it is proved (N9);
- a credit sentence sits between the corollary and its proof (N11).

Considered and left alone:
- R (ring) against 𝓡 (factor): different glyphs, and 𝓡 is defined at first use (l.42).
- The letter a ∈ A against tower level a: they live in different subsections, and both notations are standard.
- The Kronecker δ_{ba'} against the basis δ_t: different subsections; rewriting costs a line and gains little.
- No labels are needed: nothing cross-references the corollary or sections. The displays are already minimal.

## N1. The normal subgroup N → K (0 lines)
N also names SL_{3N} and the period N_ℓ in the same section. K matches "k ∈ K".

l.180, before:
```latex
Let $1\ne N\trianglelefteq G$ and $1\ne g\in N$, and let $w\ge0$ bound
```
after:
```latex
Let $1\ne K\trianglelefteq G$ and $1\ne g\in K$, and let $w\ge0$ bound
```
l.213: `Put $k=[g,h]\in N\setminus\{1\}$.` → `Put $k=[g,h]\in K\setminus\{1\}$.`
l.227: `$N\cap H$ is a nontrivial normal subgroup of` → `$K\cap H$ is a nontrivial normal subgroup of`
l.229: `$H\subseteq N$, and $e_{pq}(e_V)\in N$ for all $p\ne q$.` → `$H\subseteq K$, and $e_{pq}(e_V)\in K$ for all $p\ne q$.`
l.231: `Finally, $J=\{r\in R:e_{pq}(r)\in N\text{ for all }p\ne q\}$ is a` → `Finally, $J=\{r\in R:e_{pq}(r)\in K\text{ for all }p\ne q\}$ is a`
l.237: `$1=1-\prod_i(1-e_{T^{a_i}V})\in J$. So $J=R$ and $N=G$.\hfill$\square$` → `$1=1-\prod_i(1-e_{T^{a_i}V})\in J$. So $J=R$ and $K=G$.\hfill$\square$`

Trade-off: one letter per object. The reader no longer holds "N = period" and "N = normal subgroup" at once.

## N2. The third index in (1): k → l (0 lines)
l.106, before:
```latex
 [e_{ik}(r),e_{kj}(s)]&=e_{ij}(rs),\qquad i,j,k\text{ distinct}.
```
after:
```latex
 [e_{il}(r),e_{lj}(s)]&=e_{ij}(rs),\qquad i,j,l\text{ distinct}.
```
Trade-off: k now only means [g,h]. It also matches l.233, which already uses l as the third index.

## N3. S: drop the EJZ symbol, and define flip conjugacy without (Y,S) (+1 line)
l.110–113, before:
```latex
generate $G$, as $1=\sum_ae_a$. By Ershov and
Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ}, $\EL_n(S)$ has
property~\textup{(T)} for every finitely generated associative unital
ring $S$ and every $n\ge3$. So $G$ has property~\textup{(T)}. It is
```
after:
```latex
generate $G$, as $1=\sum_ae_a$. By Ershov and
Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ}, $\EL_n$ of every finitely
generated associative unital ring has property~\textup{(T)} for
$n\ge3$. So $G$ has property~\textup{(T)}. It is
```
l.289–291, before:
```latex
If $(X,T)$ is conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$. Does $G_X\cong G_Y$ imply that $X$ and $Y$ are flip
conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```
after:
```latex
If infinite minimal subshifts $X$ and $Y$ are flip conjugate, that is,
conjugate after possibly inverting one of the shifts, then
$G_X\cong G_Y$. Does $G_X\cong G_Y$ imply that $X$ and $Y$ are flip
conjugate, or at least strongly orbit equivalent~\cite{GPS}?
```
Trade-off:
- S now only means the set in §2.
- The question defines "flip conjugate", which rev2 uses without a definition.
- The easy direction still holds: u ↦ u^{-1} identifies the crossed products for T and T^{-1}.

## N4. Matrices in the simplicity proof: A, B → M, M′ (0 lines)
l.207, before: `$A\mapsto I_3-\psi(I_d)+\psi(A)$ embeds $\GL_d(\F_2)$ in $\GL_3(R)$. Its`
after: `$M\mapsto I_3-\psi(I_d)+\psi(M)$ embeds $\GL_d(\F_2)$ in $\GL_3(R)$. Its`

l.224–226, before:
```latex
$k^{-1}-I_3=h(ghg^{-1}-h)$ lie in it, say $k=I_3+\psi(A)$ and
$k^{-1}=I_3+\psi(B)$. As $\psi$ is injective and multiplicative,
$(I_d+A)(I_d+B)=I_d$, so $k$ is the image of $I_d+A$ and $k\in H$. Then
```
after:
```latex
$k^{-1}-I_3=h(ghg^{-1}-h)$ lie in it, say $k=I_3+\psi(M)$ and
$k^{-1}=I_3+\psi(M')$. As $\psi$ is injective and multiplicative,
$(I_d+M)(I_d+M')=I_d$, so $k$ is the image of $I_d+M$ and $k\in H$. Then
```
Trade-off: A is only the alphabet.

## N5. Take h = e_12(e_V), freeing i, j for exponents (+1 line)
l.189–196 use j both as a matrix index (h = e_ij) and as an exponent (c_j, T^jV). l.183 uses i as an exponent.

l.189–191, before:
```latex
Some $h=e_{ij}(e_V)$ with $V$ small does not commute with $g$.
Otherwise $g$ commutes with $e_{ij}(e_V)$ for every clopen $V$,
by~\eqref{eq:elementary}. Taking $V=X$ gives $g=cI_3$ with
```
after:
```latex
Some $e_{pq}(e_V)$ with $V$ small does not commute with $g$.
Otherwise $g$ commutes with $e_{pq}(e_V)$ for all $p\ne q$ and every
clopen $V$, by~\eqref{eq:elementary}. Taking $V=X$ gives $g=cI_3$ with
```
l.196, before: `gives $c=1$ and $g=1$.`
after:
```latex
gives $c=1$ and $g=1$. Conjugating $g$ by a permutation matrix changes
neither $w$ nor the small sets, so we may take $h=e_{12}(e_V)$.
```
l.220–221, before:
```latex
$ghg^{-1}-I_3=g\,e_VE_{ij}\,g^{-1}$ are sums of such products, and
$h^{-1}=h=I_3+\epsilon_{00}E_{ij}$. The image $\psi(M_d(\F_2))$ is the set
```
after:
```latex
$ghg^{-1}-I_3=g\,e_VE_{12}\,g^{-1}$ are sums of such products, and
$h^{-1}=h=I_3+\epsilon_{00}E_{12}$. The image $\psi(M_d(\F_2))$ is the set
```
Check of the WLOG step:
- A permutation matrix σ lies in EL_3(F_2) ⊆ G (over F_2 the signed Weyl elements are permutation matrices).
- g′ = σgσ^{-1} ∈ K. The entries of g′^{±1} are the entries of g^{±1}, permuted, so w and every coefficient f are unchanged, and so are the small sets.
- If g fails to commute with e_pq(e_V), then g′ fails to commute with σe_pq(e_V)σ^{-1} = e_{σ(p)σ(q)}(e_V). Take σ(p) = 1, σ(q) = 2.

Trade-off: +1 line. h becomes one explicit matrix, and each letter keeps one role in the paragraph. The generic (p,q) then agrees with l.229 and l.231.

## N6. Word length in the finite-models paragraph: no symbol (0 lines)
L names a word length at l.157–158, then L(G) at l.168 and L(X) in §2.

l.157–159, before:
```latex
of those between blocks. A word of length $L$ in these generators has
entries of degree at most $L$ in $F$, and $\varphi_\ell\circ\pi=\rho_\ell$
on these entries for large $\ell$. Applied to the entries of the word
```
after:
```latex
of those between blocks. The entries of a word in these generators lie
in $F$ and have degree at most its length, and $\varphi_\ell\circ\pi=\rho_\ell$
on these entries for large $\ell$. Applied to the entries of the word
```

## N7. Word length in §2: n → m (0 lines)
n is the rank of EL_n in the theorem and the proof. In §2 it is a word length.
- l.258: `$e_{12}(\prod_{t<n}u^{-t}e_{v_t}u^t)$ is computable from` → `$e_{12}(\prod_{t<m}u^{-t}e_{v_t}u^t)$ is computable from`
- l.259: `$v=v_0\cdots v_{n-1}$, and it is trivial if and only if $v\notin L(X)$.` → `$v=v_0\cdots v_{m-1}$, …`
- l.266: `$1$, and the words of length $n$ of $X_\alpha$ are the constant values of` → `… of length $m$ of …`
- l.267: `$c(\theta)_{[0,n)}$ on the arcs between the points $-j\alpha\bmod1$,` → `$c(\theta)_{[0,m)}$ on the arcs …`
- l.268: `$0\le j\le n$. So $\alpha$ computes $L(X_\alpha)$. Since` → `$0\le j\le m$. …`
- l.270: `the word $c(\theta)_{[0,n)}$ has $\lfloor\theta+n\alpha\rfloor$ ones,` → `the word $c(\theta)_{[0,m)}$ has $\lfloor\theta+m\alpha\rfloor$ ones,`
- l.271: `within $1$ of $n\alpha$, so $L(X_\alpha)$ computes $\alpha$. Every set` → `within $1$ of $m\alpha$, …`

m also names a recurrence position in the finite models (l.123–128). Both are locally bound integers in different sections, so no clash with the rank.

## N8. Name the proof's group once (0 lines)
l.99, before: `are the cylinder indicators, which span $\LC(X,\F_2)$. Let $G=\EL_3(R)$`
after: `are the cylinder indicators, which span $\LC(X,\F_2)$. Let $G=G_X=\EL_3(R)$`

Trade-off: the reader sees that the G of §1 and §3 is the theorem's G_X, and §2 already uses G_X.

## N9. Move the operator-algebra paragraph after the simplicity proof (+1 line)
l.169, "Since $G$ is infinite and simple", uses simplicity, which is proved only in the next subsection. The paragraph also isn't about finite models.
- Before: l.168–177 sit inside "Finite models", after l.166 `Theorem~3.3]{Pestov}.`
- After: delete l.167–177 there, and after l.237 (`\hfill$\square$`) insert:
```latex

\subsection*{Brown's formulation}
As $G$ is hyperlinear, $L(G)$ embeds in $\mathcal R^\omega$~\cite[Proposition~7.1]{Ozawa}.
Since $G$ is infinite and simple, its nontrivial conjugacy classes are
infinite and $G$ is not residually finite. So $L(G)$ is a
$\mathrm{II}_1$ factor, and $L(G)\mathbin{\bar\otimes}\mathcal R$ is a
McDuff factor that embeds in $\mathcal R^\omega$ and whose unitary group
contains $G$. This is Brown's formulation. Kirchberg proved that a
Kazhdan group with the factorization property is residually
finite~\cite[Theorem~1.1]{Kirchberg}. So $G$ does not have the
factorization property, and $C^*(G)$ does not have the local lifting
property~\cite[p.~527]{Ozawa}.
```
Trade-off: +1 line for the heading. There is no forward reference, and each subsection proves one thing. The first word becomes "As $G$ is hyperlinear," because the previous sentence is no longer adjacent. The \hfill$\square$ still closes the proof of Theorem 1.

## N10. Free-algebra generators: t → τ (0 lines)
t is the basis index of δ_t in the paragraph just before.
l.147–150, before:
```latex
Let $F=\F_2\langle t_+,t_-,t_a:a\in A\rangle$ be the free algebra, and
let $\pi\colon F\to R$ and $\rho_\ell\colon F\to M_{N_\ell}(\F_2)$ be the
ring homomorphisms with $\pi(t_\pm)=u^{\pm1}$, $\pi(t_a)=e_a$,
$\rho_\ell(t_\pm)=P^{\pm1}$ and $\rho_\ell(t_a)=D_\ell(e_a)$. Both are onto.
```
after:
```latex
Let $F=\F_2\langle \tau_+,\tau_-,\tau_a:a\in A\rangle$ be the free algebra, and
let $\pi\colon F\to R$ and $\rho_\ell\colon F\to M_{N_\ell}(\F_2)$ be the
ring homomorphisms with $\pi(\tau_\pm)=u^{\pm1}$, $\pi(\tau_a)=e_a$,
$\rho_\ell(\tau_\pm)=P^{\pm1}$ and $\rho_\ell(\tau_a)=D_\ell(e_a)$. Both are onto.
```

## N11. The credit sentence goes after the proof (0 lines)
l.247–249 sit between the corollary and its proof:
```latex
For derived topological full groups, Grigorchuk and Medynets proved that
the word problem is decidable if and only if $L(X)$ is
recursive~\cite[Theorem~1.1(3)]{GMpres}.
```
Move them unchanged to just after l.277 `\end{proof}`, preceded by a blank line.

Trade-off: the statement is followed directly by its proof, and the credit closes the section.

## Summary for main
- Recommended: N1, N2, N3, N4, N6, N7, N8, N9, N10, N11 (0 to +1 line each).
- Recommended if main accepts +1 line: N5.
- Total: +3 lines. No mathematical content changes.
- If rev3 renumbers sections (a new §2 "LEF groups"), N7 and N11 apply to the word-problems section wherever it lands.
- The rev3 §2 text should follow the same one-symbol conventions: K for normal subgroups, M for matrices, τ for free generators, m for word lengths.
