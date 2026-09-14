# sk-design-page-one: a redesigned introduction for the simple Kazhdan note

- **Base:** `simple_kazhdan_sofic_group.tex` rev4.5 (8b36733d78, md5 29d63f7944bccccbf9a91b0b2714c0b4). Line numbers `l.N` refer to rev4.5.
- **Candidate:** `$SK2/lanes/sk-design-page-one/candidate-v2.tex`, md5 1859062fef5aac672bb388e98053c722, 789 lines.
- **Scope:** only rev4.5 l.29–126 change; l.1–28 and l.127–775 are byte-identical.
- **Owner split:** main decides and lands; this is a proposal. It folds in sk-reader-grad F1–F5 (67819e1433), as main asked.

## 0. Result

- **MSI compile** (texlive 2025, pdflatex ×3): 0 errors, 0 overfull boxes, 2 underfull boxes (rev4.5 also has 2), 0 undefined references or citations. **9 pages** (rev4.5: 8).
- **Why 9 pages:** a `\pagetotal` probe shows rev4.5's page 8 was already nearly full (594.9pt of 628.7pt), so any growth beyond about 2 typeset lines moves the end of the bibliography to page 9. In the candidate, page 9 holds 132.9pt, about 10 lines. The directive allows ≤ 9 pp.
- **Source growth: +14 lines** (775 → 789). Main's budget was about +12; §3 names two cuts that give +12.
- **Page positions** (label probes):
  - page 1: Theorem 1, the definitions, the (T) item, the simplicity item;
  - page 2: the finite-models item, Theorem 2, the characterization, the credits paragraph, and §1, which starts on page 2 as before.
- **Citations:** the intro keys are rev4.5's 16 plus `Grigorchuk,Champetier`, which were already cited in §1; none dropped. Whole-file key set unchanged.
- **No mathematics changes.** Every new sentence was checked against the proofs; checks are in §2.

## 1. New order

1. **Abstract**, 5 sentences. U1's explicit host naming is kept verbatim.
2. **The question and why it mattered:** Brown 2001, Ozawa 2003, Pestov 9.1. Then Thom's non-simple example and Pestov–Kwiatkowska's hope (moved up from l.97–102).
3. **Theorem 1**, unchanged (l.57–71).
4. **Definitions and three ingredients**, replacing l.73–92:
   - F3 (minimal subshift) and the LEF definition;
   - (T), with the ring definition (F4);
   - simplicity, with the tower gloss and the minimality finish (F5);
   - finite models: what the models are and why they form expanders (F1), and the marked-group limit (F2).
5. **l.104–121 unchanged:** topological freeness, the e_ij notation, Theorem 2.
6. **Characterization** (l.123–126, reworded).
7. **Credits paragraph:** Matui and Stepanov/ClarkEdie (moved from l.85–92), Rădulescu, Gromov and Weiss (moved from l.94–96). This puts the Stepanov sentence after the sketch, one of main's two options.

## 2. OLD → NEW blocks

### Block A: abstract. OLD l.29–44 → NEW, −1 line
OLD: rev4.5 l.29–44, from `\begin{abstract}` to `\end{abstract}`.
NEW:
```
\begin{abstract}
For every infinite minimal subshift $X$, the group
$G_X=\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)}. It is a limit of finite simple
groups $\SL_{3N}(\F_2)$ whose Cayley graphs form expanders, so it is
locally embeddable into finite groups (LEF), sofic and hyperlinear. This
answers the question of Brown and Ozawa whether an infinite simple Kazhdan
group can be hyperlinear, and Pestov's sofic version of it.
A finitely generated group is LEF if and only if it is a subgroup of an
infinite finitely generated simple Kazhdan group that is a limit of finite
simple groups whose Cayley graphs form expanders, and it also has solvable
word problem if and only if the host can be chosen with solvable word
problem. One such host contains every recursively presented finitely
generated LEF group.
\end{abstract}
```
**Reason:**
- The first sentence is split, so the object and its three properties come first and the approximation second.
- "(LEF)" is introduced once and used twice.
- U1's host naming is unchanged. The second "if and only if" stays (U1/U2 wording).

### Block B: the question. OLD l.47–55, plus l.97–102 moved in → NEW, +6 (9 → 15 lines)
OLD: l.47–55 (`Can an infinite simple group…` to `…answer all three forms positively.`) and l.97–102 (`Thom constructed…` to `…can be hyperlinear~\cite{PestovKwiatkowska}.`).
NEW:
```
Can an infinite simple group with property~\textup{(T)} be hyperlinear?
Brown asked this in 2001 as a question about embeddings into unitary
groups of McDuff factors that embed in an ultrapower $\mathcal R^\omega$
of the hyperfinite $\mathrm{II}_1$ factor~\cite[\S11, Question~7]{Brown}.
Ozawa stated the hyperlinear form in 2003, noting that the full
$C^*$-algebra of such a group cannot have the local lifting
property~\cite[p.~527]{Ozawa}, and Pestov's Open question~9.1 adds the
sofic form~\cite{Pestov}. Thom constructed a finitely generated Kazhdan
group that is locally embeddable into finite groups but not residually
finite, and so lacks the factorization property~\cite{Thom}, but his
example is not simple. Pestov and Kwiatkowska wrote that a hope of
constructing groups that are not hyperlinear from property~\textup{(T)}
remained, as it was unknown whether finitely generated simple Kazhdan
groups can be hyperlinear~\cite{PestovKwiatkowska}. The groups below
answer all three forms positively.
```
**Reason:**
- The question is now followed at once by why it mattered.
- Thom's sentence says "locally embeddable into finite groups" because LEF is not yet defined at this point; its content is unchanged.
- The Pestov–Kwiatkowska sentence is verbatim.

### Block C: sketch → definitions and three ingredients. OLD l.73–92 → NEW, +7 (20 → 27 lines)
OLD: l.73–92, from `A group is LEF~\cite{VershikGordon} if…` to `…on a tower over one small cylinder.`
NEW:
```
Here $X$ is a closed shift-invariant set in which every orbit is dense, and
a group is LEF~\cite{VershikGordon} if every finite subset embeds
injectively into a finite group, preserving the products that stay in
that subset. The proof has three ingredients.
\begin{itemize}
\item \emph{Property~\textup{(T)}.} The ring $\LC(X,\F_2)\rtimes_T\Z$
consists of the finite sums $\sum_jf_ju^j$ with $f_j\in\LC(X,\F_2)$,
multiplied using $ufu^{-1}=f\circ T^{-1}$. It is finitely generated, so
$G_X$ has Kazhdan's property~\textup{(T)}~\cite{Kazhdan} by the theorem of
Ershov and Jaikin-Zapirain~\cite{EJZ}.
\item \emph{Simplicity.} A nontrivial normal subgroup contains a nontrivial
commutator lying in a copy of the finite simple group $\GL_d(\F_2)$ over a
clopen tower, a small clopen set with its disjoint translates. So it
contains this group and with it an elementary matrix, from which
minimality gives every elementary matrix.
\item \emph{Finite models.} A periodic sequence of period $N$ approximating
$X$ turns the shift into a cyclic permutation matrix and each locally
constant function into a diagonal matrix, as in the proof by Grigorchuk
and Medynets that topological full groups of minimal Cantor systems are
LEF~\cite[Theorem~2.6]{GM}. So $G_X$ is the limit of the groups
$\SL_{3N}(\F_2)$ in the space of marked groups~\cite{Grigorchuk,Champetier}:
for every word $w$ in the generators and all large $N$ in the sequence, $w$
is trivial in $G_X$ if and only if it is trivial in $\SL_{3N}(\F_2)$. These
groups are quotients of one Kazhdan group, $\EL_3$ of a finitely generated
free algebra over $\F_2$, so they form expanders as in Kassabov's
construction~\cite{Kassabov}.
\end{itemize}
```
**Reason:** these are sk-reader-grad F1–F5. After rev4.5's page 1 the reader could not explain LEF, the ring, "tower", or how one elementary matrix gives all of G_X.

**Placeholder:** the marked-limit clause ("So $G_X$ is the limit … trivial in $\SL_{3N}(\F_2)$.") stands in for sk-design-statements' named definition. Replace that one sentence with its wording.

**Checks against rev4.5:**
- **Ring:** l.240 (`ufu^{-1}=f∘T^{-1}`).
- **Models:** l.257–263 (P is cyclic, D_ℓ(f) is diagonal).
- **Limit:** l.220–233. "All large N in the sequence" equals "all large k", because N_k → ∞.
- **Expanders:** l.211–215 and l.233–235 (EL_3(F) with F free on finitely many letters τ_s, EJZ Thm 1.1, Margulis).
- **Tower:** l.175–181 (the aV, a∈B_w, are disjoint).
- **Minimality finish:** l.202–208 (J = R).

### Block D: OLD l.94–103 removed, −10 including the blank line (the lines moved to Blocks B and F)

Line total: A −1, B +6, C +7, D −10, E 0, F +12, so +14.
OLD: l.94–96 (`Hyperlinear groups were named…` to `…named by Weiss~\cite{Weiss}.`) and l.97–102 (Thom and Pestov–Kwiatkowska, now in Block B).

### Block E: characterization. OLD l.123–126 → NEW, +0
OLD: `Periodic approximations give such maps for $\LC(X,\F_2)\rtimes_T\Z$, which gives Theorem~\ref{thm:main}, and lamplighter actions show that the countable subgroups of the groups in Theorem~\ref{thm:general} are exactly the countable LEF groups (Corollary~\ref{cor:host}).`
NEW:
```
Periodic approximations of $X$ give such maps, which proves
Theorem~\ref{thm:main}, and lamplighter actions show that the countable
subgroups of the groups in Theorem~\ref{thm:general} are exactly the
countable LEF groups (Corollary~\ref{cor:host}).
```
**Reason:** removes "give … gives". The statement is unchanged.

### Block F: credits paragraph (new, after Block E), +12 including the blank line
NEW:
```
For derived topological full groups, Matui showed by an argument similar
to our proof of simplicity that a nontrivial normal subgroup meets a
simple union of alternating groups on
towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}. Simplicity also follows
from Stepanov's theorem on the normal structure of
$\GL_n$~\cite[Theorem~4.4]{Stepanov}: the ring $\LC(X,\F_2)\rtimes_T\Z$ is
simple~\cite[Corollary~4.6]{ClarkEdie}, and any $p,q$ in it satisfy
$pr+qs=0$ with $(r,s)\ne0$ by a dimension count on a tower over one small
cylinder. Hyperlinear groups were named by R\u{a}dulescu~\cite{Radulescu},
and sofic groups were introduced by Gromov~\cite{Gromov99} and named by
Weiss~\cite{Weiss}.
```
**Reason:**
- The credits are collected after the statements, so the sketch leads straight into Theorem 2 (sk-reader-grad S8).
- "by a similar argument" becomes "by an argument similar to our proof of simplicity" because the paragraph is no longer next to the sketch. The credit framing is unchanged.
- The Stepanov sentence is verbatim except that "the ring" is named.

## 3. Cuts back to +12, if main wants them

- **C1 (−1):** keep rev4.5's "by a similar argument" in Block F. The referent becomes less clear.
- **C2 (−2):** replace the `itemize` environment with three run-in `\emph{…}` heads in one paragraph. Page 1 reads worse.
- **Not recommended:** dropping F2 or F1. Those are the LEF mechanism the reader could not reconstruct.
- **Alternatives to main's Stepanov option:** moving the Stepanov sentence to the end of the Simplicity subsection (sk-reader-grad E6) saves 4 intro lines but adds 4 in §1. Net 0.

## 4. Not done here (other owners)

- The named expander-limit definition and the table belong to sk-design-statements.
- sk-reader-grad F6–F10 and E1–E5, E8 are outside l.29–126.
