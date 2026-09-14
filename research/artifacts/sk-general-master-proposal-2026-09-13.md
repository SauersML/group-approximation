# sk-general-master proposal: simplicity through a ring lemma (local annihilation)

- Lane: sk-general-master, 2026-09-13.
- Status: UNREVIEWED, queued with sk-referee-1.
- Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec92b4581553bc0dc2b0edcb99).
- Analysis: `research/artifacts/sk-general-master-2026-09-13.md`.
- **Convergence.** Lane sk-proof-minimal-conceptual independently landed the same lemma (2acfcb8559,
  `research/artifacts/sk-proof-minimal-conceptual-proposal-2026-09-13.md`):
  - Lemma 2 there: "for every finite F ∋ 1 the elements s with tFs = 0 generate R";
  - its simplicity part is 47 lines, against 49 here.
  - The note should adopt ONE text. This proposal is the additive-span variant, so its first step needs only
    `e_ij(r+s) = e_ij(r)e_ij(s)`.
  - Either text is backed by the Cairn routes landed here.

## (a1) Replace the tower subsection, l.154-227 inclusive (74 lines)

Current text, verbatim at both ends. The whole subsection is replaced.

```latex
\subsection*{A finite tower detects every normal subgroup}
Suppose the levels $T^aU$ are disjoint for all indices needed below.
For $|a|,|b|\le m$ and clopen $W\subseteq U$, put
...
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```

Replacement (49 lines). The preamble needs `\newtheorem{lemma}[theorem]{Lemma}`, one more line.

```latex
\subsection*{Normal subgroups}
\begin{lemma}\label{lem:normal}
Let $R$ be a simple ring and $n\ge3$. Suppose that for every finite
$F\subseteq R$ the elements $s$ for which some $t\ne0$ satisfies $ts=0$
and $tfs=0$ for all $f\in F$ additively span $R$. Then every normal
subgroup of $\EL_n(R)$ is central or equal to $\EL_n(R)$.
\end{lemma}

\begin{proof}
Let $N\trianglelefteq\EL_n(R)$ contain a noncentral $g$, and let $F$ be
the set of entries of $g$. By~\eqref{eq:elementary} the coefficients $s$
with $[g,e_{ij}(s)]=1$ for all $i\ne j$ form an additive subgroup, and it
is not $R$ since $g$ is not central. So some $s$ and $t$ as in the
hypothesis, and some $i\ne j$, give $\rho=[g,e_{ij}(s)]\ne1$. Every entry of
\[
 \rho-I=\bigl(gsE_{ij}g^{-1}\bigr)e_{ij}(-s)-sE_{ij}
\]
is a sum of elements $fsr$ and $sr$ with $f\in F$, so $t(\rho-I)=0$.

Put $Y=\rho^{-1}-I$, choose $Y_{qm}\ne0$, and choose $l\notin\{m,q\}$.
Since $R$ is simple, $Y_{qm}Rt\ne0$, so $z=Y_{qm}ct\ne0$ for some $c\in R$.
The relation $t(\rho-I)=0$ gives $e_{ml}(ct)\rho=\rho+ctE_{ml}$, so
\[
 v=\rho^{-1}e_{ml}(ct)\,\rho\,e_{ml}(-ct)=I+Y\,ctE_{ml}\in N.
\]
Both $v$ and $v^{-1}$ differ from $I$ only in column $l$, $v_{ql}=z$,
and $(v^{-1})_{ll}$ is a unit. For $b\notin\{l,q\}$ we have
$e_{bq}(1)v=v\,e_{bq}(1)+zE_{bl}$, and so
\[
 [e_{bq}(1),v]=e_{bl}\bigl(z\,(v^{-1})_{ll}\bigr)\ne1.
\]
Finally, $\{r\in R:e_{pq}(r)\in N\text{ for all }p\ne q\}$ is a two-sided
ideal by~\eqref{eq:elementary}. It is nonzero, since signed permutation
matrices in $\EL_n(R)$ move any elementary position to any other. So it
is $R$, and $N=\EL_n(R)$.
\end{proof}

Now let $1\ne N\trianglelefteq G$. Since $Z(G)=\{1\}$, it suffices to
check the hypothesis of Lemma~\ref{lem:normal} for $R$. Let $F\subseteq R$
be finite, with exponents at most $w$. Each $x\in X$ has a clopen
neighborhood $V$ such that $V$ and all $T^jV$ with $|j|\le w$ miss some
nonempty clopen $W$: take $W$ around a point outside $\{T^jx:|j|\le w\}$,
then shrink $V$. By compactness such sets $V$ can be chosen to partition
$X$, and then the elements $e_Vr$ span $R$. For $s=e_Vr$ and $t=e_W$ we
get $ts=0$ and
\[
 tfs=\sum_jf_j\,e_We_{T^jV}\,u^jr=0\qquad\text{for }f=\sum_jf_ju^j\in F.
\]
So $N=G$, completing the proof.\hfill$\square$
```

## (b) Why each sentence holds (for the referee; not for the note)

- **Additive subgroup, and not `R`.**
  - `e_ij(r+s) = e_ij(r)e_ij(s)`.
  - If the subgroup were `R`, `g` would commute with every generator, so it would be central.
  - The annihilated elements span `R`, so one of them lies outside the subgroup.
- **`t(ρ−I) = 0`.** The `(p,q)` entry of the first term is `g_pi·s·(g^{-1}e_ij(-s))_jq`, and the second term is `−s`.
- **`Y_qm R t ≠ 0`.** A simple ring is prime: `aRb = 0` with `a, b ≠ 0` would give `(RaR)(RbR) = 0`, while both
  factors equal `R`.
- **`e_ml(ct)ρ = ρ + ctE_ml`.** Row `m` of `ctE_ml·ρ` is `ct` times row `l` of `ρ`, which equals `ct·e_l^T`, since
  `tρ_lk = tδ_lk`.
- **The display for `v`.** `(I+ρ^{-1}ctE_ml)(I−ctE_ml)`, and `E_ml·ctE_ml = 0` since `l ≠ m`.
- **`v^{-1}`.** If `Mv = I` then `Me_k = e_k` for `k ≠ l`. Comparing `(l,l)` entries of `Mv` and `vM` shows that
  `(v^{-1})_ll` is a two-sided inverse of `v_ll`.
- **`e_bq(1)v − v e_bq(1) = zE_bl`.** With `v = I+ωe_l^T`, `E_bq ωe_l^T = ω_q E_bl` and `ωe_l^T E_bq = 0`, since
  `b ≠ l`.
- **The commutator.** `[B,v] = (vB+zE_bl)B^{-1}v^{-1} = I+zE_bl v^{-1}`, since `E_bl B^{-1} = E_bl`. Row `l` of `v^{-1}`
  is `(v^{-1})_ll e_l^T`.
- **The ideal.**
  - `e_pq(ar) = [e_pk(a), e_kq(r)]` and `e_pq(ra) = [e_pk(r), e_kq(a)]`.
  - Signed permutation matrices, e.g. `e_12(1)e_21(-1)e_12(1)`, conjugate `e_bl(r)` to `e_pq(±r)`.
  - `e_pq(−r) = e_pq(r)^{-1}`.
- **The check for `R`.**
  - `X` is infinite, so a point `y` outside the finite set exists.
  - Clopen sets separate points, and continuity of `T^j` lets us shrink `V`.
  - Subsets of `V` keep the property with the same `W`, so a finite cover refines to a partition.
  - `u^je_V = e_{T^jV}u^j`.
  - `ts = e_{W∩V}r = 0`, since the case `j = 0` is included.
- **`Z(G) = 1`** is l.114-116, kept unchanged.
- **Reused names.** `w` has the same meaning as at l.176. The indices `b, c, l, m, q` replace tower indices that no
  longer occur. `e_a` (letters, l.85) is not clashed with.

## (a2) The introduction sentence that credits the tower argument, l.58-62

Current, verbatim:
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument:
a nontrivial normal subgroup meets a finite simple matrix group
supported on a clopen tower, and therefore contains an elementary
matrix. This is an explicit elementary-matrix extraction argument,
in the normal-structure tradition described by Stepanov~\cite{Stepanov}.
```
It becomes false as a description if (a1) is adopted. Proposed replacement (5 lines):
```latex
Grigorchuk--Medynets~\cite{GM}. The new step is the simplicity argument.
It needs only that $R$ is simple and that every element of $R$ is a sum
of elements $s$ annihilated from the left, together with $fs$ for finitely
many given $f$, by some nonzero $t$. From such a pair, commutators as in
Stepanov~\cite[Lemma~4.3]{Stepanov} produce an elementary matrix.
```
- Credit wording is the user's decision. This is proposed only because the old sentence would describe a proof no
  longer in the note.
- "Lemma 4.3" comes from `un-stepanov-credit-2026-09-13.md`. sk-citations verifies it against the source before any
  use.

## (a3) Optional remark after the proof, 3 lines (user's call)

```latex
The same argument and~\cite{EJZ} show that $\EL_n(R)/Z$ is an infinite
simple Kazhdan group for every finitely generated simple ring $R$ as in
Lemma~\ref{lem:normal}, for instance the crossed product of any free
minimal action of a finitely generated group on a subshift.
```
True by reviewed nodes:
- `steinberg-algebras-have-local-annihilation` (any ample groupoid with compact infinite unit space);
- `steinberg-algebra-simple-iff-minimal-effective`;
- the centre clause of `local-annihilation-makes-projective-el-simple`.

`e_12(R)` meets the centre trivially, so the quotient is infinite. LEF is deliberately left out, since it needs exact
finite pattern models.

## (c) Length

- l.154-227: 74 → 49 lines (−25).
- Preamble: +1.
- l.58-62: 5 → 5.
- Optional remark: +3.
- Net: −24, or −21 with the remark.

For comparison, sk-simplicity-short-a's tower version is 47 lines but specific to `F_2`.

## (d) Trade-off for the reader

The simplicity proof becomes shorter and independent of the coefficient field, uses no finite simple groups or clopen
towers, and gives a reusable criterion. The reader must trust one displayed commutator computation instead of the
tower bookkeeping.

## (e) Status

- `local-annihilation-makes-projective-el-simple`: established, Lean-certified, reviewed PASS.
- New route `local-annihilation-el-simplicity-explicit-extraction`, with all identities written out: UNREVIEWED,
  queued with sk-referee-1.
- The check of the hypothesis for `R` duplicates the reviewed `steinberg-algebras-have-local-annihilation` in the case
  `R = A_{F_q}(Z ⋉ X)`, written directly.
