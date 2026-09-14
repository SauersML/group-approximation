# sk-cut-sentences proposal, part 1: what can be dropped from the note (2026-09-13)

Lane: sk-cut-sentences (roster C).
- Source: `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99, 340 lines). All line numbers below refer to it.
- Candidate note with every item applied: `$SK/lanes/sk-cut-sentences/sk-cut-sentences-candidate.tex`, 317 lines (−23, measured with wc).

The test for each sentence: does a careful reader need it to follow or trust the mathematics, or to know what is new and whom to credit?

Classes:
- KEEP;
- CUT: a restatement, metacommentary, a statement about the proof, a duplicated justification, or an unused citation;
- MERGE;
- COMPRESS.

Part 2 holds:
- items C12–C19;
- the checks M1–M5 of the replacements that carry mathematics;
- the KEEP list;
- the maximal cut and what was added back;
- hand-offs to peer lanes.

## Summary
| item | lines | class | Δ lines | also proposed by |
|---|---|---|---|---|
| C1 | 32–33 | CUT (proof description in abstract) | −1 | sk-exposition |
| C2 | 31 | COMPRESS (hence → so) | 0 | |
| C3 | 42 | CUT ("answers both forms") | −1 | sk-referee-1 P4, sk-exposition E3 |
| C4 | 55, bibitem 308–312 | CUT (unused citation) | −6 | sk-exposition keeps this credit |
| C5 | 56–62 | MERGE (credit sentences) | −1 | sk-exposition E5 |
| C6 | 96 | CUT (commutator convention) | −1 | sk-referee-1 (moves it instead) |
| C7 | 97–100 | COMPRESS | 0 | |
| C8 | 102–104 | COMPRESS (metacommentary) | −1 | sk-exposition P4, sk-simplicity-short-a A |
| C9 | 113–116 | COMPRESS (centre of G) | −1 | |
| C10 | 121 | CUT (roadmap) | −1 | sk-exposition |
| C11 | 142–152 | COMPRESS (sofic, hyperlinear) | −2 | sk-referee-2 |
| C12 | 154 | COMPRESS (title) | 0 | sk-exposition E6 |
| C13 | 171 | COMPRESS | 0 | |
| C14 | 178–193 | COMPRESS (no translates) | −3 | |
| C15 | 205–215 | COMPRESS (transvection display) | −4 | sk-referee-1 flags the display |
| C16 | 197, 217 | COMPRESS (doctrine words) | 0 | |
| C17 | 227 | COMPRESS | 0 | sk-exposition |
| C18 | 233 | COMPRESS (Consequently) | 0 | |
| C19 | 257–261 | COMPRESS (irrational representative) | −1 | sk-referee-2, sk-exposition, sk-word-problem |

Total: −23 lines. Mathematics, credit wording and the question lineage are unchanged, except for the replacements C6, C9, C14, C15 and C19, which are checked in part 2 (M1–M5).

## C1, C2. Abstract (l.27–35), −1
Before:
```
For every infinite minimal subshift $X$, the group
$\EL_3(\LC(X,\F_2)\rtimes\Z)$ is infinite, simple, finitely generated,
and has property~\textup{(T)}. It is locally embeddable into finite
groups, hence sofic and hyperlinear. This answers the questions of
Brown, Ozawa, and Pestov. The proof combines periodic approximation
with a commutator supported on a finite tower. Every Turing degree
occurs as the word-problem degree of one of these groups.
```
After:
```
For every infinite minimal subshift $X$, the group
$\EL_3(\LC(X,\F_2)\rtimes\Z)$ is infinite, simple, finitely generated,
and has property~\textup{(T)}. It is locally embeddable into finite
groups, so it is sofic and hyperlinear. This answers the questions of
Brown, Ozawa, and Pestov. Every Turing degree occurs as the word-problem
degree of one of these groups.
```
Trade-off:
- The cut sentence describes the proof, not a result. A reader of the abstract loses nothing usable, and the same content is at l.58–61.
- "hence" becomes "so" (doctrine). The credit sentence is untouched.

## C3. "both forms" (l.41–42), −1
Before:
```
Pestov's Open question~9.1 adds the sofic version~\cite{Pestov}.
The following construction answers both forms positively.
```
After:
```
Pestov's Open question~9.1 adds the sofic version~\cite{Pestov}.
```
Trade-off:
- The theorem that follows ends with "In particular, it is sofic and hyperlinear", so the sentence restates it.
- It also says "both forms" after naming three (von Neumann algebra, hyperlinear, sofic).
- The lineage sentences above it are unchanged.

## C4, C5. Second intro paragraph (l.55–65), −1 in the text, −5 in the bibliography
Before:
```
The subshift algebra is classical; see Nekrashevych~\cite{Nekrashevych}.
Property~(T) is supplied by Ershov--Jaikin-Zapirain~\cite{EJZ}.
Our finite models use the periodic-approximation mechanism of
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
a nontrivial normal subgroup meets a finite simple matrix group
supported on a clopen tower, and therefore contains an elementary
matrix. This is an explicit elementary-matrix extraction argument,
in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
```
After:
```
Property~(T) follows from a theorem of Ershov--Jaikin-Zapirain~\cite{EJZ},
and the finite models use the periodic-approximation mechanism of
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument,
an elementary-matrix extraction in the normal-structure tradition
described by Stepanov~\cite{Stepanov}: a nontrivial normal subgroup meets
a finite simple matrix group supported on a clopen tower, so it contains
an elementary matrix. Thom had already constructed a finitely generated
Kazhdan LEF group that is not residually finite~\cite[Theorem~1.4]{Thom};
his example is not simple.
```
Delete from the bibliography (l.308–312):
```
\bibitem{Nekrashevych}
V.~Nekrashevych, \emph{Growth of \'etale groupoids and simple algebras},
Internat. J. Algebra Comput. \textbf{26} (2016), 375--397.
\href{https://arxiv.org/abs/1501.00722}{arXiv:1501.00722}.
```
Trade-off:
- C4: R is defined in full at l.72–77, and [Nekrashevych] is used nowhere in the argument. "Classical" credits no one in particular, and a 2016 growth paper is not the origin of crossed products. The reader loses one pointer to further reading.
  - Disagreement: sk-exposition keeps this credit. sk-citations should rule on whether the sentence credits anything accurately.
- C5 keeps the same credit content (EJZ, GM, Stepanov, Thom) in one fewer line.
  - "supplied" (a metaphor), "This is an explicit ... argument" (a statement about the argument) and "therefore" go.
  - The opening clause about (T) and the finite models stays, because "The new step" needs something to contrast with.

## C6. Commutator convention (l.94–96), −1
Before:
```
show that the matrices $e_{ij}(s)$, for
$s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$, generate $G$.
Here $[g,h]=ghg^{-1}h^{-1}$.
```
After:
```
show that the matrices $e_{ij}(s)$, for
$s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$, generate $G$.
```
Trade-off:
- No formula in the note depends on the convention (M1 in part 2). A reader who knows either convention reads every line correctly.
- sk-referee-1 instead moves the definition to l.87. Deleting it is one line shorter.

## C7. Property (T) (l.97–100), 0
Before:
```
Ershov--Jaikin-Zapirain's theorem says that $\EL_n(R)$ has property~(T)
for every finitely generated unital associative ring $R$ and
$n\ge3$~\cite[Theorem~1.1]{EJZ}. Hence $G$ has property~(T).
It is infinite because $e_{12}(\LC(X,\F_2))$ is infinite.
```
After:
```
By Ershov--Jaikin-Zapirain~\cite[Theorem~1.1]{EJZ}, $\EL_n(S)$ has
property~(T) for every finitely generated unital associative ring $S$
and $n\ge3$, so $G$ has property~(T). It is infinite because
$e_{12}(\LC(X,\F_2))$ is infinite.
```
Trade-off:
- Same length.
- The theorem that "says", and "Hence", go.
- The bound variable no longer reuses the letter R of the fixed ring.
- The exact hypotheses of EJZ Theorem 1.1 are sk-citations' check.

## C8. Simplicity of R (l.102–104), −1
Before:
```
We will also need that $R$ is simple and $Z(R)=\F_2$.
These are standard groupoid-algebra facts~\cite{BCFS,ClarkEdie,Steinberg};
here is the direct argument. A nonzero two-sided ideal contains an
```
After:
```
The ring $R$ is simple and $Z(R)=\F_2$~\cite{BCFS,ClarkEdie,Steinberg}.
A nonzero two-sided ideal contains an
```
Trade-off:
- The fact, its credit and its proof all stay. "We will also need" and "here is the direct argument" are statements about the text.
- The brief's alternative (keep only the citation, or only the proof) goes to sk-cut-structure, with this lane's view:
  - the direct proof is 9 elementary lines;
  - citing instead makes the reader identify R with the Steinberg algebra of the transformation groupoid and trust three imports.

## C9. Centre of G (l.112–116), −1
Before:
```
$T^{-j}$-translate can be separated by a clopen set. Commuting with
$u$ then makes $f_0$ invariant, hence constant by minimality.
Finally, commuting with every $e_{ij}(1)$ forces a central element of
$G$ to be $cI_3$; commuting with all $e_{ij}(r)$ gives
$c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$.
```
After:
```
$T^{-j}$-translate can be separated by a clopen set. Commuting with
$u$ then makes $f_0$ invariant, so $f_0$ is constant by minimality.
A central element of $G$ commutes with every $e_{ij}(r)$, so it is
$cI_3$ with $c\in Z(R)^\times=\{1\}$. Thus $Z(G)=\{1\}$.
```
Trade-off: one sentence does the job of two. The two steps (scalar from e_ij(1), central coefficient from e_ij(r)) are matrix arithmetic a reader does at sight (M4).

## C10. Roadmap sentence (l.119–122), −1
Before:
```
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.
We construct such models for $R$, and then apply them entrywise.
```
After:
```
A group is LEF if every finite subset embeds injectively into a finite
group, preserving all products that stay in that subset.
```
Trade-off: the sentence previews the next 27 lines, which the reader is about to read. l.146 ("include the entries of its elements") states the entrywise step where it happens.

## C11. Sofic and hyperlinear (l.142–152), −2
Before:
```
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
After:
```
window occurs in $y$. Taking $N$ larger than twice the largest absolute
exponent makes the corresponding cyclic diagonals distinct, so nonzero
differences also remain nonzero.

For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$, so $G$ is LEF.
LEF groups are sofic, and sofic groups are hyperlinear~\cite{Pestov}.
```
Trade-off:
- LEF ⇒ sofic ⇒ hyperlinear is standard and cited. The mechanism (regular actions, then permutation matrices) is textbook. The reader loses the mechanism and saves two lines.
- sk-citations should confirm that [Pestov] states both implications.
