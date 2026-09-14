# sk-stable-rank-b proposal: simplicity in about 20 lines through Stepanov's theorem (2026-09-13)

- Lane: sk-stable-rank-b.
- Status: UNREVIEWED; review requested from sk-referee-1.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).
- Cairn:
  - `amenable-crossed-products-meet-stepanov-condition-b` (+ `-proof`);
  - route `subshift-elementary-group-simple-stepanov-proof` into `subshift-elementary-group-is-simple-modulo-centre`;
  - open `subshift-crossed-product-ring-has-bass-stable-rank-at-most-two`.
- Sources read: `research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md`.

**Stable-rank shortcut (the brief): not proposed.** It needs `sr(R) ≤ 2`, which is open here and has no short proof.
The Stepanov route below needs no stable rank and is shorter than any stable-rank argument would be.

## (a) Current text and replacement

### A. l.154-227: the whole simplicity section
Current (verbatim):
```text
154  \subsection*{A finite tower detects every normal subgroup}
155  Suppose the levels $T^aU$ are disjoint for all indices needed below.
 ...  [l.156-226 unchanged from the frozen copy: E_{ab}(W), B_m(U), (eq:absorb), the choice of h, k=[g,h],
      kappa, H_W, the p=q commutator display, simplicity of GL_d(F_2), the level ideal I_N]
227  simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
The full 74 lines are in the frozen copy. Every line from 154 to 227 is deleted.

Replacement (verbatim LaTeX):
```latex
\subsection*{Normal subgroups}
For $p,q\in R$ there are $r,s\in R$, not both $0$, with $pr+qs=0$.
Indeed, let $w$ bound the absolute values of the exponents in $p$ and
$q$, put $h=2w+1$, and choose a nonempty clopen $U$ such that every
coefficient $f$ of $p$ and $q$ has $f\circ T^m$ constant on $U$ for
$|m|\le 3w$. For $\rho\in\F_2^h$ put $r_\rho=\sum_{0\le j<h}\rho_ju^je_U$.
Since $fu^m=u^m(f\circ T^m)$, we get
$pr_\rho=\sum_{|m|\le 3w}(P\rho)_m\,u^me_U$ for an
$(h+2w)\times h$ matrix $P$ over $\F_2$, and likewise
$qr_\sigma=\sum_{|m|\le 3w}(Q\sigma)_m\,u^me_U$. As $2h>h+2w$, some
nonzero $(\rho,\sigma)$ has $P\rho+Q\sigma=0$; take $r=r_\rho$ and
$s=r_\sigma$.

Let $1\ne N\trianglelefteq G$. For $a\in\GL_3(R)$, the claim applied to
$a_{12},a_{13}$ gives a nonzero column $\alpha=(0,r,s)^T$ with
$\alpha_1=(a\alpha)_1=0$. This is condition~(b) of Stepanov's
theorem~\cite[Theorem~4.4]{Stepanov}, and condition~(a) there holds
trivially because $R$ is simple. So every subgroup of $\GL_3(R)$
normalized by $G$ is central in $\GL_3(R)$ or contains
$G$~\cite[\S1.6(3)]{Stepanov}. Since $Z(G)=1$, we get $N=G$.\hfill$\square$
```

### B. l.78-82: the partition sentence
Current:
```text
78  Minimality and infiniteness imply that $T$ has no periodic points.
79  For each $L$, every point therefore has a clopen neighborhood $U$ with
80  $U\cap T^jU=\varnothing$ for $0<|j|\le L$. Compactness gives finite
81  clopen partitions with this property, refining any prescribed clopen
82  partition.
```
Replacement:
```latex
Minimality and infiniteness imply that $T$ has no periodic points.
For each $L$, every point therefore has a clopen neighborhood $U$ with
$U\cap T^jU=\varnothing$ for $0<|j|\le L$.
```
The compactness sentence was used only at l.178-180, which A deletes. The first two sentences stay, for the simplicity
and centre of `R` (l.106-112).

### C. l.58-62: the credit sentence for simplicity (USER DECISION: wording and novelty claim)
Current:
```text
58  Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
59  a nontrivial normal subgroup meets a finite simple matrix group
60  supported on a clopen tower, and therefore contains an elementary
61  matrix. This is an explicit elementary-matrix extraction argument,
62  in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
```
Replacement:
```latex
Grigorchuk--Medynets~\cite{GM}. Simplicity comes from Stepanov's
normal-structure theorem~\cite{Stepanov}: its linear-dependence
hypothesis holds because any two ring elements $p,q$ satisfy $pr+qs=0$
with $(r,s)\ne0$, by a dimension count on one cylinder.
```

### D. l.32-33 in the abstract (USER DECISION)
Current:
```text
32  Brown, Ozawa, and Pestov. The proof combines periodic approximation
33  with a commutator supported on a finite tower. Every Turing degree
```
Replacement:
```latex
Brown, Ozawa, and Pestov. The proof combines periodic approximation
with Stepanov's normal-structure theorem. Every Turing degree
```

## (b) Complete proof text
A is the complete simplicity proof. It uses l.102-116 unchanged: `R` is simple, `Z(R) = F_2`, `Z(G) = 1`. The label
`eq:absorb` is cited only inside the deleted block. `eq:elementary` stays, since it is used at l.94, l.185 and l.247.

## (c) Length change
- A: 74 → 20 lines (−54).
- B: 5 → 3 lines (−2).
- C: 5 → 4 lines (−1).
- D: 0.
- Total about −57 lines of the 340.

Compared with the peers:
- sk-simplicity-short-a: 74 → 47 lines.
- sk-simplicity-short-b: one commutator into a finite tower group.

This proposal is shorter than both, and the difference is a citation in place of the finite-group mechanism.

## (d) Reader-facing trade-off
The proof becomes much shorter and removes tower subrings, absorption and finite simple groups. In exchange the reader
trusts Stepanov's Theorem 4.4 (J. Math. Sci. 95 (1999), one page, from Lemmas 4.1 and 4.3 by standard commutator
calculations), which the note already cites. The note loses its self-contained, explicit extraction of a finite simple
subgroup, which l.58-61 currently call "the new step".

## (e) Status
- All three Cairn items are unreviewed and queued with sk-referee-1.
- Stepanov's §1.5, §1.6(3), Theorem 4.4 and its proof were read from the page images by this lane, after un-stepanov-credit.
- The only mathematics new to the note is the pair-dependence count (§3 of the route artifact).
- A free strengthening at no cost: the same text proves `EL_n(LC(X,F_q) ⋊ Z)/Z` simple for every `n ≥ 3` and `q`, and
  the GL-level sandwich for simple amenable crossed products.
