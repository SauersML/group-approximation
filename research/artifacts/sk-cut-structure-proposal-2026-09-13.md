# sk-cut-structure proposal: which parts of the note should exist

Lane sk-cut-structure, 2026-09-13.
- Target: `simple_kazhdan_sofic_group.tex`, disk version of 16:46 (frozen copy `sk/manuscript-disk-1646.tex`, md5 7b3dc4ec…).
  Line numbers refer to that copy.
- Scope: structure only (which parts exist). Sentence-level wording belongs to sk-cut-sentences and sk-arbitrary, and
  prior-art credit wording to sk-novelty and sk-citations. Nothing is applied to any `.tex` at the repo root.
- Full candidate notes in the lane dir `sk/lanes/sk-cut-structure/`: `candidate-A-minimal.tex`,
  `candidate-B-current-scope-cut.tex`, `candidate-C-enriched-slots.tex`.
- MSI pdflatex, two passes each: disk note, A, B and C all have 0 errors, 0 overfull boxes and 0 undefined references.

## 0. Summary

| note | lines | pages | content |
|---|---|---|---|
| disk (current) | 340 | 4 | Theorem 1 + Turing corollary |
| **B** current scope, structurally cut | **311** | 4 | same statements; three unused ring facts and four citations removed |
| **B′** B with §2 replaced by a counting corollary | ~293 | 4 (est.) | Theorem 1 + "continuum many" by counting markings |
| **A** minimal answer | **268** | **3** | Theorem 1 only |
| **C** enriched | 312 + slot budgets (≤ ~350) | 4–5 | B + verified corollaries from other lanes |

The main finding is a structural cut that holds in every candidate:
- **The proof never needs that R is simple, nor that Z(R) = F_2.** The level ideal `I_N` contains a clopen indicator
  `e_W`, and an ideal containing an indicator is `R`, because finitely many translates of `W` cover `X`.
- **Z(G) = 1 needs only aperiodicity and F_2^× = {1}.**
- So the paragraph at l.102–116 shrinks from 15 lines to 7, three citations disappear (BCFS, Clark–Edie-Michell,
  Steinberg), and the ending gains 3 lines.
- Node on main: `subshift-f2-ring-indicator-ideals-and-centreless-el3` with its `-proof` route (landed b6e4795499,
  unreviewed, queued with sk-referee-1).

## 1. Structural changes in every candidate

### S1. Drop the Nekrashevych sentence and its bibitem
(a) l.55, verbatim: `The subshift algebra is classical; see Nekrashevych~\cite{Nekrashevych}.`
Replacement: nothing. Also delete the bibitem at l.308–311.
(c) −1 text line, −5 bibliography lines.
(d) The ring is defined in full at l.73–77, and no argument uses the reference. The reader loses only a pointer to
groupoid-algebra background.
(e) No mathematics involved.

### S2. Replace the simplicity-of-R and centre paragraph (l.102–116)
(a) Current text, verbatim:
```latex
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
(a, b) Replacement, verbatim:
```latex
The center of $G$ is trivial. A central element commutes with every
$e_{ij}(1)$, so it is $cI_3$ for a unit $c\in R$, and commuting with
every $e_{ij}(e_V)$ gives $ce_V=e_Vc$ for all clopen $V$. Write
$c=\sum_jf_ju^j$. Then $f_j=0$ for $j\ne0$: otherwise a point in the
support of $f_j$ and its $T^{-j}$-translate can be separated by a
clopen set. So $c\in\LC(X,\F_2)$ is invertible, and $c=1$ because
$\F_2^\times=\{1\}$.
```
Delete the bibitems BCFS (l.278–282), ClarkEdie (l.284–288) and Steinberg (l.323–326).
- Why the replacement is complete:
  - The `u^j`-coefficient of `e_Vc−ce_V` is `f_j(e_V−e_{T^jV})`, which at `x ∈ V` with `T^{-j}x ∉ V` equals `f_j(x)`.
  - `c = f_0` and `cr = 1` give `f_0 g_0 = 1`, so `f_0` is nowhere zero, and so `f_0 = 1`.
  - Minimality is not used. Aperiodicity (l.78) is.
- Where each fact is used. `Z(G)=\{1\}` is used at l.187, and nowhere else. "R is simple" was used only at l.226
  (see S3). `Z(R)=F_2` was used only to get `Z(G)=1`.

(c) −8 text lines, −16 bibliography lines.
(d) The proof is shorter and trusts no outside theorem. The reader loses the true but unused fact that R is simple
with centre F_2.
(e) Node `subshift-f2-ring-indicator-ideals-and-centreless-el3`, part (2). Unreviewed.

### S3. End of the proof: translates instead of simplicity of R
(a) l.223–227, verbatim:
```latex
Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
(b) Replacement, verbatim:
```latex
Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. So $I_N$ contains $e_W$ and its
translates $u^ne_Wu^{-n}=e_{T^nW}$. By minimality and compactness,
finitely many translates cover $X$, so $I_N$ contains
$1=1-\prod_i(1-e_{T^{n_i}W})$. Thus $I_N=R$ and $N=G$, completing the
proof.\hfill$\square$
```
(c) +3 text lines.
(d) Minimality is now used once, visibly, at the only place it matters. The disk text uses it inside the unused
simplicity proof.
(e) Node part (1). Unreviewed.

Net for S2+S3: −5 text lines, −16 bibliography lines, three fewer citations, no new fact.

### S4. Abstract: drop the sentence about the proof (l.32–33)
(a) `The proof combines periodic approximation with a commutator supported on a finite tower.`
Replacement: nothing. (c) −1 line.
(d) It is a statement about the proof, which the introduction (l.56–62) already gives. sk-cut-sentences may reach
the same verdict; this artifact records it as a structural item because it affects all three candidates.

### S5. Kept on purpose (decided, no change)
- **Theorem clauses.**
  - "infinite" is needed, since the trivial group is simple, Kazhdan and LEF.
  - "sofic and hyperlinear" is the form in which Pestov and Ozawa ask the question.
  - "finitely generated" is implied by property (T) for discrete groups, but it costs two words and helps readers
    from approximation theory, so it is neutral.
- **Thom sentence (l.63–65).** It is the closest earlier result and says exactly what is new (simplicity). The reader
  needs it to judge novelty.
- **Stepanov sentence (l.60–62).** The technique is prior (Stepanov 1997; see `un-stepanov-credit-2026-09-13.md`), so
  credit must stay. Any rewording belongs to sk-novelty and the user.
- **GM and EJZ sentences.** They are credit for the two imported mechanisms.
- **Aperiodicity and partitions (l.78–82), absorption (l.168–173), the generation of H_W (l.205–215), the LEF
  definition.** Each is used. Shortening them is sentence-level work (sk-arbitrary, sk-simplicity-short-*).
- **Optional, not applied.** Merge the S2 paragraph into l.185–187 ("Otherwise ... g commutes with every e_ij(r)
  ..."). This saves 1–2 lines but interrupts the tower argument.

## 2. The word-problem section: three options (user's scope choice)
- **Keep (candidate B).** Keep §2, preferably with sk-word-problem's replacement
  (`sk-word-problem-proposal-2026-09-13.md`, −6 lines, unreviewed).
  - Gains: the formula `WP(G_X) ≡_T L(X)`, every Turing degree, solvable word problem for computable X, and continuum
    many. It is the note's only statement beyond the answer to the question.
- **B′ (counting).** Replace l.229–262 by the following, verbatim:
```latex
\section{Continuum many groups}

\begin{corollary}
There are continuum many pairwise nonisomorphic groups $G_X$.
\end{corollary}

\begin{proof}
For a word $v=v_0\cdots v_{n-1}$, relations~\eqref{eq:elementary}
give a fixed word $W_v$ in the generators $e_{ij}(s)$ whose value is
$e_{12}(\prod_{t<n}u^{-t}e_{v_t}u^t)$, and $W_v=1$ in $G_X$ if and only if
$v$ does not occur in $X$. So the group $G_X$ marked by these
generators determines the language of $X$, and so determines $X$.
A countable group has countably many finite generating tuples, and
there are continuum many infinite minimal subshifts over
$\{0,1\}$, for example the Sturmian subshifts~\cite{MorseHedlund}.
\end{proof}
```
  and the abstract sentence l.33–34 by `There are continuum many of these groups up to isomorphism.`
  - (c) −18 lines against the disk section, −11 against sk-word-problem's version.
  - (d) The reader loses the Turing degrees and the computability of the Sturmian language. The reader gains a proof
    with no computability theory; the only fact taken on trust is that Sturmian subshifts of different slopes differ.
  - Why it is complete:
    - If `G_Y ≅ G_X`, pulling back Y's generating tuple gives a generating tuple of `G_X` whose relations determine
      `L(Y)`, and a subshift is determined by its language.
    - `G_X` has countably many tuples of that length, so each isomorphism class contains countably many `X`.
    - The marked-determination step is the lower bound already in l.242–249.
  - (e) The mathematics is already reviewed on main:
    - `continuum-many-simple-kazhdan-lef-groups`: PASS, un-review-open part1 §1.2. Its route requires
      `marked-subshift-elementary-group-determines-language` and `continuum-many-infinite-minimal-binary-subshifts`
      (PASS, §1.6).
    - Only the LaTeX wording above is new.
- **Drop (candidate A).** Delete l.229–262, the abstract sentence at l.33–34, `\newtheorem{corollary}`, and the
  MorseHedlund bibitem.
  - (c) −43 lines, and the note fits on 3 pages.
  - (d) The note becomes exactly the answer. The reader loses every statement about the size or variety of the
    family.

**Lane recommendation on reader merits.**
- Keep a §2. "Continuum many pairwise nonisomorphic" is the cheapest statement that the construction is a family and
  not one example.
- Choose between B (with sk-word-problem's text) and B′ by whether the user wants computability in the note: B is
  stronger, B′ is shorter.
- If sk-rigidity-* proves a short isomorphism theorem, "continuum many" should move there, and §2 could go (A plus
  the rigidity corollary).

## 3. Candidate C: slots for verified corollaries
C is B with `% SLOT` comments. Include only items a verifier has PASSed.
- **C-gen:** EL_n for all n ≥ 3, and F_q with G/Z(G) [sk-coefficients, sk-general-master, sk-arbitrary,
  sk-hypotheses-sharp]. Budget 0 to +2 lines.
  - Note for them: over F_q with q > 2, S2 needs one more step. Commuting with `e_ij(u)` makes `c` invariant, so
    constant by minimality; then the centre is the scalars `cI` with `c ∈ F_q^×` that lie in `EL_3`.
- **C-fp:** the Kirchberg sentence after l.65 [sk-questions-oa, unreviewed]. Budget +2 lines of text, +5 of
  bibliography.
- **C-cor:** a "Further properties" section with one corollary, each item with a proof of a few lines:
  - (i) the finite models are expanders converging to G_X in the space of marked groups [sk-expanders-limits]. Budget
    +8.
  - (ii) every f.g. RF (or LEF) group embeds in some G_X [sk-universal-embedding-a/b]. Budget +10.
  - (iii) `[[T]] ↪ G_X` [sk-subgroups]. Budget +3.
  - (iv) isomorphism rigidity [sk-rigidity-*]. Budget +6 to +12; it can replace the counting in B′.
- **C-wp:** sk-word-problem's replacement, −6 lines.

Reader trade-off for C: each slot answers or sharpens a further question. At more than ~50 added lines the note stops
being short, so cap C at two corollary items.

## 4. Status
- Landed: node `subshift-f2-ring-indicator-ideals-and-centreless-el3` + `-proof` (b6e4795499). Unreviewed; review
  requested in `sk/queue/sk-referee-1.txt`.
- Candidates A, B and C compile cleanly (MSI, pdflatex × 2). `diff` from the disk note to B contains only the S1–S4
  changes.
- Not verified by a second reader: the S2/S3 replacement texts. They use only arguments already in the note; the node
  is queued for review.
- The B′ mathematics is reviewed on main (§2); its LaTeX wording is not.
