# rev4.4 fixes from sk-perfect-a (whole-paper correctness), on rev4.3 md5 0648e5f8
Verdict: ERROR 0, GAP 0, UNCLEAR 9, TYPO 6. Every step re-derived; statements match proofs; refs resolve.

PRIORITY: U1, U2, U5, then U4.
- U1 (l.182–198): the unit e of A_V clashes with the identity e in ε_ee and B_{2w}∖{e}. Rename it 1_V:
  - l.182 `with unit $1_V=\sum_a\epsilon_{aa}$`
  - l.183 `$y\mapsto(1-1_V)I_3+y$`
  - l.197 `$y=1_VI_3+(k-I_3)$`
  - l.198 `$y'=1_VI_3+(k^{-1}-I_3)$ satisfy $yy'=y'y=1_VI_3$, so $k=(1-1_V)I_3+y\in H_V$`
  - (perfect-d suggested ε; use 1_V, which is clearer.)
- U2 (l.385–402, 428–429): lamps f → c throughout the lamplighter paragraph (`x\mapsto\delta x+c`, `$c$ finitely supported`, `$(\delta,c)\ne(e,0)$`, `+c(h)`, `\operatorname{supp}c`). Whitehead product: `for $v=v_1$, $v_2$ and $(v_2v_1)^{-1}$ is $\operatorname{diag}(v_1v_2v_1^{-1}v_2^{-1},1,1)$`.
- U3 (l.107): `and $e_{ij}(r)=I_n+rE_{ij}$, with $E_{ij}$ the matrix unit, is an elementary matrix.` Merge with PROSE-2 / R2: "We write $e_{ij}(r)=I_n+rE_{ij}$, with $E_{ij}$ the matrix unit, for the elementary matrices."
- U4 (l.241–242, +1 line): "Minimality and infiniteness imply that $X$ has no isolated points and $T$ has no periodic points, so $X$ is a Cantor set and the action is topologically free."
- U5 (l.360–361, 365): "multiply the first coordinate from the left by $\gamma$ on the levels $m\ge0$"; "where $f$ multiplies the level $m$ from the left by".
- U6 (l.441–443): "gives $\ell$, the levels where $f$ changes (the exponent sums of $\beta$ before the letters $h_\gamma^{\pm1}$), and the values of $f$ there as words in $E$." Merge with perfect-d R1.
- U7 (l.479): "set~\cite[Theorem~4.21]{KMS}, which no single recursive bound allows; compare~…"
- U8 (l.327): "every $G_Y$ with $L(Y)$ recursive (Corollary~\ref{cor:wp})."
- U9 (l.482): "The groups $G_X$ cannot serve as such hosts: $\SL_3(\Z)$ lies in no $G_X$."
- T1 (l.71–73): the double "by"; use perfect-b PROSE-1 wording.
- T2 (l.302): "They raised the question which" → "They asked which".
- T3 (l.527–528): S → D: `$D\subseteq\mathbb N$ has the degree of $[0;1+\chi_D(0),1+\chi_D(1),\dots]$`.
- T4 (optional): §1 commutator k → x (perfect-d agrees).
- T5 (optional): the §3 degree bound w → W.
- T6 (optional): the §3 coordinate h → η.
