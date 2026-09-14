# sk-el2-fq proposal: every finite field in the note

Lane sk-el2-fq, 2026-09-13.
- **Mathematics:** `subshift-el-2-simple-modulo-centre-every-finite-field` with its route (UNREVIEWED, queued with
  sk-verify-7), and the artifact `research/artifacts/sk-el2-fq-all-fields-2026-09-13.md`.
- **Line numbers:** main's note at revision 2 (e80dcf20ad, md5 4ad49212…).

## Firewalls for any wording (main's decision log, item 23)
- Never say "with the same proof" for F_q. The binary text finds its noncommuting root through LC(X,F_2)^× = {1}. Over
  F_q it needs the roots e_ij(e_V u), a tower of height w+1, SL_d(F_q) in place of GL_d(F_2), and a non-scalar step.
- The expander and marked-limit clause is proved for n ≥ 3 only. EL_2 over the free algebra has no (T).
- Never write "n = 2 loses (T)".

## Option R3 (recommended default; every F_q, n ≥ 3; no new citation)

### (a) Current text, l.59–61
```latex
is locally embeddable into finite groups \textup{(LEF)}, sofic and
hyperlinear. The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$
for every $n\ge3$, with $\SL_{nN}(\F_2)$ in place of $\SL_{3N}(\F_2)$.
```
Unchanged. Insert after the end of the simplicity proof (l.237, `So $J=R$ and $N=G$.\hfill$\square$`):
```latex
\subsection*{Other finite fields}
For every finite field $\F_q$ and $n\ge3$, the group
$\EL_n\bigl(\LC(X,\F_q)\rtimes_T\Z\bigr)$ has property~\textup{(T)}, its
centre consists of scalar matrices, and its quotient by the centre is
simple and LEF. In the proof of simplicity use the roots $e_{ij}(e_V)$
and $e_{ij}(e_Vu)$, since only scalar matrices commute with all of them,
and towers of height $w+1$. Then $k=[g,h]$ lies in a copy of
$\GL_d(\F_q)$, and $k-I_n$ vanishes on the $n$ basis vectors of the top
level, so $k$ is not scalar. So $N$ meets the copy of $\SL_d(\F_q)$,
which is perfect with simple central quotient, in a noncentral normal
subgroup, hence contains it, and the level step finishes as before. The
models of the quotient live in $\mathrm{PGL}_{nN}(\F_q)$.
```

### (c) Length
+12 source lines (about +8 typeset lines), and no new bibitem.

### (d) Reader-facing trade-off
- **Gain:** the theorem's mechanism is shown to be independent of F_2, and the F_2 choice reads as a convenience, not
  a necessity. This settles the arbitrariness question sk-arbitrary raised (item 8).
- **Cost:** the paragraph compresses step 2 of the artifact (the product formula with the extra shift c) and the
  perfectness argument into two sentences. A careful reader needs about ten minutes with pencil to reconstruct them.
- **Nothing new to trust:** only the simplicity of PSL_d(F_q) and perfectness of SL_d(F_q), both classical.

## Option R2 (only if the note adopts sk-el2's rank-two subsection, its Option A)
Same insertion, with the first sentence replaced by
```latex
For every finite field $\F_q$ and $n\ge2$, the group
$\EL_n\bigl(\LC(X,\F_q)\rtimes_T\Z\bigr)$ has property~\textup{(T)}, its
centre consists of scalar matrices, and its quotient by the centre is
simple and LEF.
```
and "the level step finishes as before" replaced by "the level step finishes as before, for $n=2$ through the three
Peirce blocks of $e_V$". It costs no extra lines beyond R3 and relies on the EJZK criterion that the rank-two subsection
already cites.

## Option 0
No change: the note stays over F_2, and the result stays in Cairn.

## (e) Status
- Unreviewed: `subshift-el-2-simple-modulo-centre-every-finite-field` (+ route), queued with sk-verify-7.
- The n ≥ 3 case is `subshift-elementary-group-is-simple-modulo-centre` (on main). The artifact's §5 "n ≥ 3" bullet
  derives it along the note's architecture, which is exactly what R3 compresses.
- For R2, (T) in rank two rests on `complementary-full-idempotents-make-el-2-kazhdan` (unreviewed, queued with
  sk-verify-4).
