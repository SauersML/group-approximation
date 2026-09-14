# sk-lef-growth: manuscript proposal (RULES §6)

Lane sk-lef-growth, 2026-09-13. Line numbers refer to `$SK/manuscript-disk-1646.tex`.

**Verdict.** The mathematics goes to Cairn: `subshift-elementary-group-lef-growth-complexity-bounds` and `sturmian-elementary-group-lef-growth-is-exp-r-squared`, both UNREVIEWED.
- For the note I recommend **Option 1**: one sentence, +3 lines, no new machinery.
- **Option 2** is a Sturmian remark. I do not recommend it under the shortness constraint. It is recorded so the user can choose it.
- **Option 0** is no change.

## Option 1 (recommended): explicit size of the finite models

(a) Current text, l.146-149:
```
For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
```
Replacement:
```
For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
For the ball of radius $r$ in the generators above, $k=2r$ suffices,
and the construction gives $N\le 2R$ whenever every word of $X$ of
length $R$ contains all words of length $4r+1$.
```

(b) The proof is the sentence together with the note's own construction:
- A word of length at most r in the generators has entries Σ_{|j|≤r} f_j u^j with windows in [−r, r].
- The products needed to multiply two such matrices use windows in [−2r, 2r], so the words of length 4r+1 must agree.
- There are at least 4r+2 of them, so N > 2r.
- The segment w of l.125-129 fits between an occurrence of a 4r-word and its next occurrence after R letters, so |w| ≤ 2R.

(c) Length: +3 lines.

(d) Reader trade-off: the finite models become quantitative (the model size is bounded by the recurrence function), with no new machinery. The reader checks one window count.

(e) Status: part 1 Theorem A of `research/artifacts/sk-lef-growth-bounds-2026-09-13-part1.md`, node `subshift-elementary-group-lef-growth-complexity-bounds`, item 1. UNREVIEWED.

Coordination note for sk-lef-short, which may replace l.118-152: the same sentence fits any version of the model. The data needed are windows of length 4r+1 for the r-ball, and N ≤ 2R_X(4r+1).

## Option 2 (not recommended for the note): the Sturmian remark

(a) Insert after l.152, and add `\newtheorem{remark}[theorem]{Remark}` after l.9:
```
\begin{remark}
Let $L(r)$ be the least order of a finite group admitting an injective
partial homomorphism of the ball of radius $r$ in $G_X$. If $X$ is
Sturmian, then $\log L(r)$ is of order $r^2$, for every slope. The upper
bound is the construction above: a closed walk through all edges of a
Rauzy graph of $X$ gives $N\le 8r+4$. For the lower bound, let
$q_n\le 2m<q_{n+1}$ be continued-fraction denominators of the slope.
Two letter conditions at distance $q_n\pm1$ cut out a clopen set $W$
with $W\cap T^tW=\varnothing$ for $0<|t|\le 2m$. Conjugation by
$\operatorname{diag}(u,u^{-1},1)$ multiplies entries by $u$, so the
transvections of $H_W\cong\GL_d(\F_2)$, $d=3(2m+1)$, have length $O(m)$,
and so do the relations of its unitriangular subgroup $U$. These
relations hold in a finite model of a ball of radius $Cm$, so $U$ maps
to the model, and the kernel is trivial because it would contain the
central transvection. So $L(Cm)\ge|U|=2^{d(d-1)/2}$.
\end{remark}
```

(b) The remark compresses Lemmas 0, 1, 3 and 4, and Theorems C and D of part 2. A fully rigorous in-note version needs about 25 lines.

(c) Length: about +18 lines as written; about +28 with complete proofs.

(d) Reader trade-off:
- Gain: a sharp quantitative theorem, LEF growth exp(Θ(r²)) for every Sturmian slope. It is the G_X analogue of Bradford's Question 7.2 on the Sturmian family.
- Cost: new notions (LEF growth, Rauzy graphs, continued fractions), a proof that is only sketched at this length, and no bearing on the questions the note answers.

(e) Status: `sturmian-elementary-group-lef-growth-is-exp-r-squared`, UNREVIEWED.

## Option 0: no change
Reader trade-off: neutral.

## What should NOT go in the note
- "LEF growth separates slopes" is false: part 2 (D1) refutes `elementary-group-lef-growth-separates-subshifts`.
- If the note later says the family G_X has continuum many isomorphism types, LEF growth cannot supply that on the Sturmian family. The Turing-degree corollary or a rigidity theorem must.
