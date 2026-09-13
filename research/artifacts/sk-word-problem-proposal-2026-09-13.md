# sk-word-problem proposal: the word-problem section of the note

Lane `sk-word-problem`, 2026-09-13. Target: `simple_kazhdan_sofic_group.tex`, disk version of 16:46
(frozen copy `manuscript-disk-1646.tex`, md5 7b3dc4ec…), lines 229–262. Status: proposed text is UNREVIEWED.
Review requested from sk-referee-2.

## 0. Verdict on the current text
No ERROR. Every step checks, including the orientation `u^{-t}e_a u^t = e_{[x_t=a]}` (from `ue_Uu^{-1}=e_{TU}`
and `(Tx)_n=x_{n+1}`), and the fact that the upper-bound algorithm queries only finitely many words.

Findings:
- **UNCLEAR, l.233–234.** "continuum many isomorphism classes of these groups": "these groups" can be read as
  all infinite simple Kazhdan LEF groups, or as the `G_X`. The proof gives the stronger reading, continuum many
  pairwise nonisomorphic `G_X`, at no extra length.
- **UNCLEAR, l.238–239.** The identity `WP(G_X) ≡_T L(X)` is proved but hidden inside the proof. Stating it in the
  corollary costs one line and is the useful formula.
- **GAP (minor), l.251.** `X_α` is never defined, so the letter `1` and the slope convention are implicit.
- **UNCLEAR, l.253–254.** "words of length n are determined by the cyclic order of the distinct rotation endpoints"
  does not say how. The reader has to reconstruct the arc coding.
- **GAP (minor), l.255–256.** "the minimum number of 1's in a word of length n is ⌊nα⌋" is true, but it needs both
  values `⌊nα⌋`, `⌊nα⌋+1` to occur (true because `X_α` is aperiodic). The bound `|k−nα| < 1` suffices, and it has
  a one-line proof: `c(y)_{[0,n)}` has exactly `⌊y+nα⌋` ones, since `⌊y+(t+1)α⌋−⌊y+tα⌋=1` exactly when
  `y+tα mod 1 ≥ 1−α`.
- **UNCLEAR, l.257–260.** "interleave the characteristic sequence of a noncomputable set with 1's in a binary
  expansion" is hard to parse. The interleaving is also unnecessary: for a noncomputable set the plain binary
  expansion is already not eventually periodic. One uniform choice handles every degree, the computable degree
  included (continued fractions).

## 1. Proposal A (recommended): replace l.229–262

### (a) Current text, verbatim (l.229–262)
```latex
\section{Every word-problem degree}

\begin{corollary}
Every Turing degree occurs as the word-problem degree of an infinite
simple Kazhdan LEF group. Consequently, there are continuum many
isomorphism classes of these groups.
\end{corollary}

\begin{proof}
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
\end{proof}
```

### (a, b) Replacement, verbatim LaTeX (this is the complete proof as it would appear)
```latex
\section{Word problems}

\begin{corollary}
The word problem of $G_X$ has the Turing degree of the language $L(X)$
of $X$. Every Turing degree occurs, so there are continuum many pairwise
nonisomorphic groups $G_X$.
\end{corollary}

\begin{proof}
Multiplying out a word in the generators gives a matrix with entries
$\sum_jf_ju^j$, each $f_j$ a table on words, using $uf=(f\circ T^{-1})u$.
The word is trivial if and only if the tables of its difference from
$I_3$ vanish on $L(X)$, so $L(X)$ computes the word problem. Conversely,
by~\eqref{eq:elementary} a word for $e_{12}(\prod_{t<n}u^{-t}e_{v_t}u^t)$
is computable from $v=v_0\cdots v_{n-1}$, and it is trivial if and only if
$v\notin L(X)$.

For irrational $\alpha\in(0,1)$ let $X_\alpha$ be the infinite minimal
Sturmian subshift, the closure of the codings $c(y)$, $y\in[0,1)$, with
$c(y)_t=1$ if and only if $y+t\alpha\bmod1\ge1-\alpha$~\cite{MorseHedlund}.
Its words of length $n$ are the constant values of $c(y)_{[0,n)}$ on the
arcs between the points $-j\alpha\bmod1$, $0\le j\le n$, so $\alpha$
computes $L(X_\alpha)$. The word $c(y)_{[0,n)}$ has $\lfloor y+n\alpha\rfloor$
ones, within $1$ of $n\alpha$, so $L(X_\alpha)$ computes $\alpha$. Every set
$S\subseteq\mathbb N$ has the degree of the irrational number
$[0;1+\chi_S(0),1+\chi_S(1),\dots]$, and the degree of the word problem is
an isomorphism invariant.
\end{proof}
```

Checks behind each sentence, for the verifier:
- **Upper bound.** The generators are `e_ij(s)` with `s ∈ {1,u,u^{-1},e_a}`, and over `F_2` inverses are the
  same generators. Tables are functions on `A^{[−ρ,ρ]}`, and `(fu^i)(f'u^j) = f(f'∘T^{-i})u^{i+j}` enlarges the
  radius by `|i|`. An entry is zero in `R` iff each table vanishes on the words of `L(X)` of its length. Since
  `Z(G_X)=1`, "trivial" means `= I_3`. The queries are computed in advance from the word.
- **Lower bound.** By induction, `e_ij(s_1⋯s_m) = [e_ik(s_1), e_kj(s_2⋯s_m)]` gives a word for `e_12` of a
  monomial. The product is the cylinder indicator of `[v]` at coordinates `0..n−1`, which is `0` iff
  `v ∉ L(X)`, and `e_12(0) = I_3`.
- **Arcs.**
  - The `t`-th coordinate of `c(y)` changes only where `y+tα ≡ 0` or `y+tα ≡ 1−α`, that is at
    `y ≡ −tα` or `y ≡ −(t+1)α`. For `t<n` these are the points `−jα mod 1`, `0≤j≤n`, so `c(y)_{[0,n)}` is
    constant on each open arc.
  - At an endpoint, the right-continuous coding equals the value on the arc to the right.
  - By shift invariance and closure, `L_n(X_α) = {c(y)_{[0,n)} : y ∈ [0,1)}`.
  - The points are distinct because `α` is irrational. So their circular order, and a rational point in each
    arc, are computable from `α` using strict comparisons only.
- **Balance.**
  - `⌊y+(t+1)α⌋−⌊y+tα⌋ ∈ {0,1}`, and it equals `1` iff `{y+tα} ≥ 1−α`. Summing over `t<n` gives
    `#ones = ⌊y+nα⌋`.
  - Since `0≤y<1`, `nα−1 < ⌊y+nα⌋ < nα+1`.
  - Limit points of `X_α` have the same language, so every word of length `n` gives `α` within `1/n`.
- **Continued fractions.** Proved in the node `continued-fraction-real-realizes-every-turing-degree`: the
  digits lie in `{1,2}`, and each digit is one strict comparison of `α` with a rational number computed from the
  earlier digits.
- **Continuum.** There are `2^ℵ0` degrees, and each realized degree gives a group `G_{X_α}`. Distinct degrees
  give nonisomorphic groups, so the family is explicit and pairwise nonisomorphic.

### (c) Length
The current block is 34 lines (l.229–262), and the replacement is 28 lines: **−6 lines**.

### (d) Reader-facing trade-off
- The statement is stronger at the same length: it names the formula `WP(G_X) ≡_T L(X)`, and it says
  "pairwise nonisomorphic `G_X`" where the current text says "isomorphism classes of these groups".
- The proof is shorter, defines `X_α`, and proves the balance count in one clause, so the reader no longer trusts
  the minimum-count fact.
- One uniform choice of `α` replaces a two-case construction.
- New machinery: none beyond the standard fact that an irrational number and its continued fraction digits
  compute each other.

### (e) Status
- `WP(G_X) ≡ L(X)`: reviewed PASS on main (`subshift-elementary-group-word-problem-degree`,
  `subshift-elementary-group-word-problem-equals-language`; the reduction is even truth-table).
- `L(X_α) ≡_T α`: reviewed PASS, folklore (`sturmian-language-is-turing-equivalent-to-angle`).
- Every degree, simple Kazhdan LEF: reviewed PASS (`every-turing-degree-is-a-simple-kazhdan-lef-word-problem`).
- New and UNREVIEWED: `continued-fraction-real-realizes-every-turing-degree` (+ `-proof`), the route
  `every-turing-degree-simple-kazhdan-lef-via-continued-fractions`, and the proposed LaTeX above.
- The citation for the Sturmian coding and minimality (Morse–Hedlund, or Lothaire, *Algebraic Combinatorics on
  Words*, ch. 2) belongs to sk-citations.

## 2. Options considered and not recommended
- **Truth-table degrees.** `WP(G_X) ≡_tt L(X)` holds (un-open-5 Theorem 4). But the step `L(X_α) ≤_T α` uses
  unbounded approximations, so "every tt-degree occurs" is not established. Saying "tt" adds a notion without
  a stronger headline.
- **Conjugacy problem.** Not pursued. It would add length without answering a published question I know of.
- **Replace the corollary by isomorphism rigidity (sk-rigidity-*).** A theorem such as "G_X ≅ G_Y ⇒ strong
  orbit equivalence" would import isomorphism theory for `EL_3` in characteristic 2. The Turing corollary is
  self-contained and explicit, and it also exhibits solvable word problems (computable `α`, e.g. the Fibonacci
  slope `(3−√5)/2`). Keep it unless a rigidity result lands with a short verified proof. In that case
  "continuum many" could move there, and this section could drop its last sentence.
- **Optional clause, neutral (exposition's call).** "For example, $G_X$ has solvable word problem when $X$ is the
  Fibonacci subshift."
- **Section title.** "Word problems" vs the current "Every word-problem degree" is neutral (exposition's call).
- **A different family realizing every degree** (substitutive or Toeplitz subshifts with a prescribed skeleton).
  Deciding membership of a word needs a recurrence bound, and recovering the set from the language needs pattern
  detection. Both take more lines than the two Sturmian sentences.
