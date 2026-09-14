# sk-open-1 proposal: what the note should end with

Lane `sk-open-1`, 2026-09-13. Lens: the single most beautiful theorem this note could end with. Line numbers refer to `sk/manuscript-disk-1646.tex` (md5 7b3dc4ec…). Everything new here is UNREVIEWED.

## 1. This lane's theorem: normal subgroups are subsystems

Result (on main, d2384bf1e8 + b0fe8ee829; proofs in `sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md`). Setting: X ⊆ A^Z a subshift without periodic points, n ≥ 3, G = EL_n(LC(X,F_2) ⋊ Z).
- Every ideal of R is the ideal I_Y of a closed invariant Y (`aperiodic-subshift-ring-ideals-are-invariant-open-sets`).
- Every N ⊴ G satisfies E_n(R, I_Y) ≤ N ≤ ker π_Y for a unique Y (`aperiodic-subshift-el-normal-subgroups-are-sandwiched`).
- The gap ker π_Y / E_n(R, I_Y) is the image of K_2(n, R_Y). The stable K_2 vanishes (ABC; sk-open-4 Theorem K), and the unstable n = 3 case is OPEN (`aperiodic-subshift-ring-unstable-k2-vanishes`). If it vanishes, normal subgroups are exactly the subsystem kernels and every quotient of G is some G_Y (`elementary-group-normal-subgroups-are-subsystem-kernels`, open).
- Corollary: G_X is simple iff X is minimal. This duplicates sk-hypotheses-sharp's `subshift-elementary-group-simple-iff-infinite-minimal`, which is more general (any field, modulo centre). This lane's copy was retired.

### P1 (optional, +11 lines): a closing subsection of §1
(a) Current text, l.223-227, verbatim:
```latex
Finally, $I_N=\{r\in R:e_{12}(r)\in N\}$ is a two-sided ideal:
permutation matrices in $G$ move any elementary position to any other,
and~\eqref{eq:elementary} gives addition and multiplication on either
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
Replacement: keep l.223-227 unchanged and insert after l.227:
```latex
\subsection*{Normal subgroups and subsystems}
The proof describes every normal subgroup when $X$ is only assumed to
have no periodic points. The argument for the simplicity of $R$ shows
that every two-sided ideal of $R$ consists of the elements whose
coefficients vanish on some closed invariant set $Y$. Take $Y$ with
$I_N$ of this form, and let $\pi_Y$ restrict coefficients to $Y$. Then
$e_{ij}(I_N)\subseteq N\le\ker\pi_Y$. Indeed, if $\pi_Y(g)\ne1$, the centre
computation over $Y$ gives an $h$ with $\pi_Y([g,h])\ne1$, so the corner
$\kappa$ is nontrivial at a point of $Y$, and the argument puts some
$e_W$ with $W\cap Y\ne\varnothing$ into $I_N$. So $G_X$ is simple exactly
when $X$ is minimal.
```
(b) The proof is the text above, together with the note's l.175-227.
(c) Length: +11 lines.
(d) Trade-off: stronger at +11 lines with no new machinery, since the hypothesis "minimal" becomes exactly the condition for simplicity. But it is about non-minimal systems, which the note never needs. It overlaps sk-hypotheses-sharp's sharpness sentence, so the reader should get at most one of the two.
(e) Status: the nodes above, unreviewed and queued with sk-referee-1.

### P1' (recommended instead, +1 sentence)
If the note states sharpness at all, use sk-hypotheses-sharp's one-sentence version ("infinite and minimal is exactly simplicity") and leave the sandwich in Cairn.

## 2. Ranking the candidates for the note's final theorem
Status is taken from the lanes' landed proposals; I did not re-verify their proofs.

1. **Every finitely generated residually finite group is a subgroup of an infinite simple Kazhdan LEF group** (sk-universal-embedding-a, unreviewed).
   - Most beautiful and highest impact: it turns "one example" into "every RF group sits inside one". Without (T) it is Kionke–Schesler.
   - Cost: an Ore overgroup Δ ⊇ Γ with Γ ≤ [Δ,Δ], a residually finite Toeplitz subshift over Δ, and the proof run over Δ.
   - Recommended as the note's closing corollary IF a verifier PASSes it and the proof fits in ~15 lines.
2. **The finite models are finite simple groups SL_{3N}(F_2), with an explicit uniform Kazhdan constant, converging to G_X in the space of marked groups** (sk-expanders-limits).
   - Reviewed on main (`finite-simple-groups-converge-to-simple-kazhdan-group`, PASS). The earlier version b965d63ba carried it.
   - Useful and short. It replaces the partial models of l.146-152 by honest quotients of one Kazhdan group.
   - Recommended in any case, as the end of the finite-models subsection, not as the final theorem.
3. **Normal subgroups ↔ subsystems** (this lane): Cairn plus at most one sentence (P1').
4. **Other acting groups** (sk-general-actions-a): a remark at most. The headline should stay over Z.
5. **Rigidity G_X ≅ G_Y ⇔ flip conjugacy**: open (sk-rigidity-intrinsic). Keep it out, and keep continuum many from Turing degrees.

**Verdict.** If candidate 1 passes review, the note should end with it. Otherwise it should end with candidate 2 inside §1 and keep the word-problem corollary as the final section.
