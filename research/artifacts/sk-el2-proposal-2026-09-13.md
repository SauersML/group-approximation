# sk-el2 proposal: rank two in the note

Lane sk-el2, 2026-09-13. Line numbers refer to the note at main tip 44210ab9bb (386 lines, md5 4ad49212…, last commit
e80dcf20a). The frozen disk copy predates revision 2, so its numbers do not apply here.

Mathematics:
- `complementary-full-idempotents-make-el-2-kazhdan` and `subshift-el-2-is-simple-kazhdan-lef` (artifact parts 1 and 2), both UNREVIEWED
  and queued with sk-verify-4.
- Imports used: `strongly-root-graded-groups-have-kazhdan-root-unions` (EJZK) and `elementary-linear-semidir-pair-relative-t`.

## Firewall for any wording
- The theorem's expander and marked-limit clause is proved only for n ≥ 3. It uses a uniform Kazhdan constant for
  the universal lattice EL_3(F⟨x⟩). EL_2(F⟨x⟩) lacks (T), because it surjects onto EL_2(F[t]) (EJZK footnote).
  So a rank-two sentence must not claim expanders.
- Simplicity in rank two is proved over F_2 only. Over F_q the unit trick fails.
- Never write "n = 2 loses (T)".

## Option A (recommended): rank two stated and proved

### (a) Current text, l.60–61
```latex
hyperlinear. The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$
for every $n\ge3$, with $\SL_{nN}(\F_2)$ in place of $\SL_{3N}(\F_2)$.
```
Replacement:
```latex
hyperlinear. The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$
for every $n\ge3$, with $\SL_{nN}(\F_2)$ in place of $\SL_{3N}(\F_2)$, and
$\EL_2\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ is also an infinite, finitely
generated, simple Kazhdan LEF group.
```

### (a, b) Insert after l.237 (`... So $J=R$ and $N=G$.\hfill$\square$`), before `\section{Word problems}`
```latex
\subsection*{Rank two}
Let $G=\EL_2(R)$, $M=M_2(R)$, and let $W\subseteq X$ be clopen with
$\varnothing\ne W\ne X$. Put $E_1=e_WE_{11}$, $E_2=e_WE_{22}$ and
$E_3=(1-e_W)I_2$. Finitely many translates of $W$, and of $X\setminus W$,
cover $X$, so $ME_AM=M$ for every $A$. For $A\ne B$ the abelian groups
$Y_{AB}=I_2+E_AME_B$ lie in $G$ and generate it. For distinct $A,B,C$,
$x\in E_AME_B$ and $y\in E_BME_C$ we have $[I_2+x,I_2+y]=I_2+xy$. So the
$Y_{AB}$ form a strong grading of $G$ by the root system $A_2$, and their
union is a Kazhdan subset of $G$~\cite{EJZK}. With $S=e_WRe_W$, the group
$\langle Y_{12},Y_{21}\rangle\cong\EL_2(S)$ acts on $Y_{13}Y_{23}$ through
finitely many copies of $S^2$, so $(G,Y_{13}Y_{23})$ has relative
property~\textup{(T)}~\cite{Kassabov,EJZK}. The opposite ring gives the
same for $Y_{31}Y_{32}$, and $Y_{12}$, $Y_{21}$ lie in bounded products of
these groups. So $G$ has property~\textup{(T)}, and it is finitely generated.

For simplicity take $w\ge1$ in the argument above, so that $d=2(2w+1)$;
it gives $e_{12}(e_V)\in N$. Take $W=V$. Then
$J_{AB}=\{x\in E_AME_B:I_2+x\in N\}$ satisfies $J_{AB}ME_C\subseteq J_{AC}$
and $E_CMJ_{AB}\subseteq J_{CB}$. Starting from $e_VE_{12}\in J_{12}$, every
$J_{AB}$ equals $E_AME_B$, so $N=G$. The finite models of
$\EL_2(R)$ are those above, with $2m_\ell$ in place of $3m_\ell$.
```

### New bibitem (alphabetically after `EJZ`)
```latex
\bibitem{EJZK}
M.~Ershov, A.~Jaikin-Zapirain, and M.~Kassabov,
\emph{Property~\textup{(T)} for groups graded by root systems},
Mem. Amer. Math. Soc. \textbf{249} (2017), no.~1186.
\href{https://arxiv.org/abs/1102.0031}{arXiv:1102.0031}.
```
- The arXiv number is verified: the source was fetched on MSI.
- The Memoirs volume and number are recalled and not checked on Crossref; sk-citations should confirm them.
- Main's import nodes quote the source statements verbatim.

### (c) Length
- +2 lines in the theorem.
- +26 lines in the new subsection.
- +5 bibliography lines.
- Total about +33 lines, about 9% of the note.

### (d) Reader-facing trade-off
- **Gain.** The statement is stronger and sharp: rank two is the smallest rank, since EL_1 is trivial, and the
  arbitrary "n ≥ 3" disappears.
- **Cost.** The reader must trust the strong-grading criterion of Ershov–Jaikin-Zapirain–Kassabov, in place of the
  EJZ theorem alone. The subsection compresses two routine checks: the relative (T) bookkeeping and the fact that the
  Y_AB lie in and generate G. Each takes a few lines in artifact part 1.
- **Unchanged.** Nothing else in the note changes.

### (e) Status
- Unreviewed: both claims and this text. Review requests are in `sk/queue/sk-verify-4.txt`.
- Imports: established on main.
- Checked from the EJZK TeX source: `thm:main2`, the grading and strong-grading definitions, the A_2 sufficient
  condition, the relative (T) sentence, and the rank-one footnote.

## Option B: statement only, no proof
Replace l.60–61 as in Option A, and add one clause citing EJZK, with no subsection.
- Cost: +2 text lines, +5 bibliography lines.
- Not recommended: the rank-two proof needs the three-block level argument and the grading, and these are not
  "replace 3 by 2".

## Option 0: no change
Keep "for every $n\ge3$". The rank-two result stays in Cairn. This is the right call only if main keeps the note at
its present length.
