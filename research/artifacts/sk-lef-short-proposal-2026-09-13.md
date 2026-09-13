# sk-lef-short: the shortest LEF proof for the simple Kazhdan sofic group note (proposal, 2026-09-13)

Lane `sk-lef-short`. Target text: `simple_kazhdan_sofic_group.tex`, frozen copy `manuscript-disk-1646.tex`
(md5 7b3dc4ec92b4581553bc0dc2b0edcb99), l.118-152, "Finite models".

## 0. Summary
- **Replacement B (recommended).** Shortest: 26 source lines against 35. The two informal paragraphs, "for any fixed
  finite list of sums and products ..." and "include the entries ... all intermediate sums and products", become two
  exact statements: the models are additive and multiplicative for large k, and they separate nonzero elements.
  "Its length N can be chosen arbitrarily large" is replaced by the automatic bound N_k ≥ #L_{2k+1}(X) → ∞.
- **Replacement A.** 31 source lines. Same proof, stated as a unital embedding R ↪ ∏_ω M_{N_k}(F_2). Use A if the
  note wants the ultraproduct sentence of §6b: G lies in an ultraproduct of the finite simple groups SL_{3N_k}(F_2).
- **Optional clause (§6a, +2 lines).** An explicit period N_k < 2m, where every word of X of length m contains all
  words of length 2k+1. The proof is on main as a Cairn node, together with the radius-to-model-size dictionary, so
  the LEF growth of G_X is below 2^{36 Rec_X(4r+1)^2}.
- No new mathematics is needed for the theorem. The embedding is item 3 of the existing node
  `minimal-subshift-algebra-is-simple-lef-ring`, and GL_n LEF is `exactly-matricial-rings-have-lef-general-linear-groups`
  (review PASS, un-verify-3).

## 1. Current text (verbatim, l.118-152)
```
\subsection*{Finite models}
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.
We construct such models for $R$, and then apply them entrywise.

For each $k$, there is a periodic sequence $y=w^\infty$ with exactly
the same words of length $2k+1$ as $X$. Indeed, minimality implies
uniform recurrence. In a point of $X$, choose two occurrences of the
same word of length $2k$, separated by a segment $w$ long enough to
contain every word of length $2k+1$. Repeating this segment introduces
no new word of that length at the join. Its length $N$ can be chosen
arbitrarily large.

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

For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```
I found no error in it. Small defects:
- "evaluate its local table along y" leaves implicit why the value is well defined: the windows of y are words of X.
- "hence" goes against the prose doctrine.
- "Its length N can be chosen arbitrarily large" is an extra step, and the lower bound on N comes for free.

## 2. Replacement B (recommended, verbatim LaTeX)
```
\subsection*{Finite models}
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.

Fix $x\in X$ and $k\ge0$. By minimality every word of $X$ occurs in $x$,
and $x_{[0,2k)}$ recurs at arbitrarily large positions. Choose such a
position $N_k$ with all words of length $2k+1$ of $X$ occurring in
$x_{[0,N_k+2k)}$. This word begins and ends with $x_{[0,2k)}$, so it has
period $N_k$, and the $N_k$-periodic sequence $y_k$ that agrees with $x$
on $[0,N_k)$ has the same words of length $2k+1$ as $X$. So $N_k$ is at
least the number of these words, which tends to infinity because $X$ is
infinite.

On $\F_2^{\Z/N_k\Z}$ let $P\delta_n=\delta_{n+1}$. For $f$ depending only
on coordinates in $[-k,k]$ let $D_k(f)\delta_n=f(T^ny_k)\delta_n$, where
$f(T^ny_k)$ is the value of $f$ at any point of $X$ that agrees with
$T^ny_k$ on $[-k,k]$, and put $\varphi_k(\sum_jf_ju^j)=\sum_jD_k(f_j)P^j$.
Since $PD_k(f)P^{-1}=D_k(f\circ T^{-1})$, for all $r,s\in R$ the
identities $\varphi_k(r+s)=\varphi_k(r)+\varphi_k(s)$ and
$\varphi_k(rs)=\varphi_k(r)\varphi_k(s)$ hold for large $k$. For large
$k$ a nonzero $f_j$ gives $D_k(f_j)\ne0$, and the terms with $|j|<N_k/2$
have disjoint supports, so $\varphi_k(r)\ne0$ for $r\ne0$. For a finite
$F\subseteq G$ and large $k$, applying $\varphi_k$ to the entries of the
elements of $F$ and of their inverses gives an injective map
$F\to\GL_{3N_k}(\F_2)$ that preserves the products staying in $F$. So $G$
is LEF, and so it is sofic and hyperlinear~\cite{Pestov}.
```

## 3. Replacement A (ultraproduct form, verbatim LaTeX)
The first paragraph and the last sentences differ from B. The periodic-word paragraph is identical.
```
\subsection*{Finite models}
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset. It suffices to
embed $R$ unitally in an algebraic ultraproduct
$\prod_\omega M_{N_k}(\F_2)$, with $\omega$ a nonprincipal ultrafilter
on $\mathbb N$. Then $G\subseteq\GL_3(R)$ embeds in
$\prod_\omega\GL_{3N_k}(\F_2)$, and finitely many products and
inequalities in $G$ hold in almost every factor.

[periodic-word paragraph exactly as in B]

On $\F_2^{\Z/N_k\Z}$ let $P\delta_n=\delta_{n+1}$. For $f$ depending only
on coordinates in $[-k,k]$ let $D_k(f)\delta_n=f(T^ny_k)\delta_n$, where
$f(T^ny_k)$ is the value of $f$ at any point of $X$ that agrees with
$T^ny_k$ on $[-k,k]$. Put
\[
  \varphi\Bigl(\sum_j f_ju^j\Bigr)=\Bigl(\sum_j D_k(f_j)P^j\Bigr)_k,
\]
with $0$ in the finitely many coordinates where some $D_k(f_j)$ is
undefined. Since $PD_k(f)P^{-1}=D_k(f\circ T^{-1})$ for large $k$,
$\varphi$ is a unital ring homomorphism. For large $k$ a nonzero $f_j$
gives $D_k(f_j)\ne0$, and the terms with $|j|<N_k/2$ have disjoint
supports, so $\varphi$ is injective. So $G$ is LEF, and so it is sofic
and hyperlinear~\cite{Pestov}.
```

## 4. Every step, checked (for the referee lanes)
Conventions are those of the note: (Tx)_n = x_{n+1}, u f u^{-1} = f∘T^{-1}, and D_k(f)δ_n = f(T^n y_k)δ_n.
1. **Minimality.** Every forward orbit is dense (its ω-limit set is closed, invariant and nonempty). So every word of X
   occurs in x at arbitrarily large positions, x_{[0,2k)} in particular.
2. **Period.** If x_{[N,N+2k)} = x_{[0,2k)}, then x_i = x_{i-N} for i ∈ [N,N+2k), so x_{[0,N+2k)} has period N. The
   N-periodic y with y_{[0,N)} = x_{[0,N)} therefore agrees with x on [0,N+2k).
3. **Windows.** A (2k+1)-window of y, translated by a multiple of N, starts at some i ∈ [0,N) and ends at i+2k ≤ N+2k-1.
   So it lies inside x_{[0,N+2k)}, a word of X. Conversely every word of L_{2k+1}(X) occurs in x_{[0,N+2k)}, which is a
   subword of y. So L_{2k+1}(y) = L_{2k+1}(X).
4. **N_k → ∞.** An N-periodic sequence has at most N distinct windows of each length, so N_k ≥ p_X(2k+1). Since X is
   infinite, p_X is unbounded: m+1 distinct points differ on some [-n,n], which gives m+1 distinct words of length
   2n+1.
5. **D_k well defined.** If f depends only on coordinates in [-k,k], then (T^n y_k)_{[-k,k]} = y_{[n-k,n+k]} ∈ L(X). So
   a point z ∈ X with z_{[-k,k]} equal to it exists, and f(z) does not depend on the choice of z. D_k is additive and
   multiplicative on such f.
6. **Commutation.** P D_k(f) P^{-1} δ_n = f(T^{n-1}y_k) δ_n = (f∘T^{-1})(T^n y_k) δ_n. If f depends on [-ρ,ρ], then
   f∘T^{-1} depends on [-ρ-1,ρ-1]. So the identity holds once ρ+1 ≤ k.
7. **Homomorphism for large k.** φ_k((f u^i)(g u^j)) = φ_k(f·(g∘T^{-i}) u^{i+j}) = D_k(f) D_k(g∘T^{-i}) P^{i+j}
   = D_k(f) P^i D_k(g) P^j, once k exceeds the windows of f and of g∘T^{-i}. Extend bilinearly. Additivity holds once k
   exceeds all windows, and D_k(1) = I.
8. **Separation.** If r = Σ_{|j|≤w} f_j u^j ≠ 0, pick f_j ≠ 0 and a point where f_j = 1. Its window is a word of X,
   contained in a (2k+1)-word, which occurs in y_k. So D_k(f_j) ≠ 0 for large k. The term D_k(f_j)P^j is supported on
   the entries (n+j,n), and once N_k > 2w distinct exponents occupy disjoint entries. So φ_k(r) ≠ 0.
9. **Entrywise (B).** For finite F ⊆ G, collect the finitely many identities needed: the products of pairs of entries
   of g, h ∈ F with gh ∈ F; the products of entries of g and g^{-1}, which give φ_k(g)φ_k(g^{-1}) = I, so the images
   are invertible; the sums; and nonvanishing of the entries of g-h for g ≠ h. All hold for large k. So g ↦ φ_k(g) is
   injective on F, lands in GL_{3N_k}(F_2), and preserves products staying in F.
10. **Ultraproduct (A).** M_3(∏_ω M_{N_k}) = ∏_ω M_{3N_k}, and an element of an ultraproduct of rings is a unit iff
    ω-almost every coordinate is a unit. Łoś for finitely many identities and inequalities gives LEF for subgroups
    of ∏_ω GL_{3N_k}(F_2).
11. **Sofic and hyperlinear.** The citation is unchanged from the current text. The verified locators on main
    (`pestov91-literature-background-2026-09-13-part2.md` §12):
    - Elek–Szabó, Math. Ann. 332 (2005), p. 422: "It is known [8],[19],[6] that the LEF-groups are sofic."
    - Elek–Szabó, p. 423: "We shall prove that countable sofic groups are hyperlinear (Theorem 2)."
    - Pestov, Theorem 3.3 (recorded there).
    For sk-citations: whether `\cite{Pestov}` alone is the right locator for both implications.

## 5. Length and reader trade-off
- Current l.118-152: 35 source lines, including 3 blank lines.
- B: 26 lines (−9). A: 31 lines (−4). A + §6a: 33. B + §6a: 28.
- **Trade-off (B).** Shorter, and every step is an exact statement where the current text has two informal
  paragraphs. It adds no machinery.
- **Trade-off (A).** A little longer. It needs the algebraic ultraproduct, and in exchange it states a structural fact
  (R ⊆ ∏_ω M_N(F_2)) that supports the one-line strengthening of §6b.

## 6. Optional variants
### 6a. Explicit period (+2 lines, after "Choose such a position $N_k$ ... $x_{[0,N_k+2k)}$.")
```
(If every word of $X$ of length $m$ contains all words of length $2k+1$,
the first recurrence at a position $N_k\ge m-2k$ works, and $N_k<2m$.)
```
Proof: the word x_{[m-2k,2m-2k)} has length m. So it contains every word of length 2k+1, hence every word of length
2k, x_{[0,2k)} included, starting at a position in [m-2k, 2m-4k]. And x_{[0,N_k+2k)} ⊇ x_{[0,m)} contains all
(2k+1)-words.
- **Trade-off.** One useful number, needed for any quantitative use of the models (LEF growth, explicit first models).
  It is not needed for the theorem.
- The consequence for the group is on main: node `subshift-lef-models-period-below-twice-recurrence`. For linearly
  recurrent X (primitive substitutions such as Fibonacci; Durand, recalled), the r-ball of G_X embeds partially in
  GL_{3N}(F_2) with N = O(r), so the LEF growth is at most 2^{O(r^2)}.

### 6b. Ultraproduct of finite simple groups (+1 line, only with A)
After "So $G$ is LEF": add "Since $\GL_{3N_k}(\F_2)=\SL_{3N_k}(\F_2)$ is simple, $G$ is a subgroup of an ultraproduct
of finite simple groups." The note already uses the simplicity of GL_d(F_2) (l.217-218). **Trade-off.** A strictly
stronger approximation statement for one line. Coordinate with sk-expanders-limits, whose marked-limit corollary
subsumes it if adopted.

### 6c. Keep the current proof, with the minimal repair
If the user keeps l.118-152:
- "hence nonzero differences also remain nonzero" becomes "so nonzero differences also remain nonzero".
- "Its length $N$ can be chosen arbitrarily large." becomes "Its length $N$ is at least the number of words of length
  $2k+1$ of $X$, so it tends to infinity with $k$."

## 7. Status
- The mathematics of B and A is `minimal-subshift-algebra-is-simple-lef-ring` item 3 plus
  `exactly-matricial-rings-have-lef-general-linear-groups` (PASS). I re-derived every step in §4.
- New node landed with this artifact: `subshift-lef-models-period-below-twice-recurrence` (+ `-proof`). It is
  unreviewed, and review is requested from sk-referee-1. Recalled inputs: Morse–Hedlund p_X(n) ≥ n+1 (only for the
  lower bound N_k ≥ 2k+2 used in the ball dictionary) and Durand's linear recurrence of primitive substitutions (only
  for the example).

## 8. Infra note
`sk/manuscript-main-b965d63ba.tex` was the `git show` output of commit 0103d58eb: zsh `$T:s…` fired the colon modifier.
The real b965d63ba manuscript is 970 lines (md5 3a11a03d23cb580bd629d313a6b7a1c1), copied to this lane's `src/`.
Main has been told. Its §§329-457 ("Local embeddability") had the same ultraproduct proof in ~125 lines. Codex
compressed that to 35, and B is 26.
