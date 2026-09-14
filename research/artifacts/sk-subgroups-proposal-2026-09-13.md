# sk-subgroups proposal for `simple_kazhdan_sofic_group.tex`

Lane `sk-subgroups`, 2026-09-13. Line numbers refer to `$SK/manuscript-disk-1646.tex` (md5 7b3dc4ec…).
Mathematics: `research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part1.md` and `-part2.md`. UNREVIEWED, queued with sk-referee-2.

## The fact
For every infinite minimal subshift `X`, `G_X` contains the commutator subgroup `[[T]]'` of the topological full group.
- That group is infinite, finitely generated and simple (Matui), and amenable (Juschenko–Monod).
- So the infinite simple Kazhdan group `G_X` contains an infinite finitely generated simple amenable group, and both come from the same subshift.
- The proof is two identities: Whitehead's identity, and the commutator identity for diagonal matrices.

The whole full group `[[T]]` also embeds, through `g ↦ diag(w_g, u^{−I(g)}, 1)` (part 1, Theorem B). Its proof needs the index map and a Kakutani–Rokhlin argument, and `[[T]]` is not simple, so I do not recommend it for the note.

## Option 1 (recommended if the note keeps any consequences): one paragraph at the end of the introduction
(a) Current text, l.63-65:
```latex
Thom had already constructed a finitely generated Kazhdan LEF group
that is not residually finite~\cite[Theorem~1.4]{Thom}; his example
is not simple.
```
Replacement: the same three lines, followed by
```latex

The group $G_X$ contains the commutator subgroup $[[T]]'$ of the
topological full group of $X$. If a homeomorphism $g$ equals $T^{n_i}$ on
the pieces $U_i$ of a clopen partition, then $w_g=\sum_i u^{n_i}e_{U_i}$ is
a unit of $R$, and $g\mapsto w_g$ is an injective homomorphism. Whitehead's
identity puts $\operatorname{diag}(a,a^{-1},1)$ in $G_X$ for every unit $a$,
so the product
$\operatorname{diag}(a,a^{-1},1)\operatorname{diag}(b,b^{-1},1)
\operatorname{diag}((ba)^{-1},ba,1)=\operatorname{diag}(aba^{-1}b^{-1},1,1)$
also lies in $G_X$. So $g\mapsto\operatorname{diag}(w_g,1,1)$ embeds $[[T]]'$,
which is infinite, finitely generated and simple~\cite[Theorems~4.9
and~5.4]{Matui} and amenable~\cite[Theorem~A]{JM}.
```
The notation `u`, `e_U`, `R` is introduced only at l.69-77. If the paragraph goes in the introduction, either move it to the end of §1 (Option 2) or write `\LC(X,\F_2)\rtimes_T\Z` for `R`. Option 2 avoids the forward reference.

New bibitems, in alphabetical position after `GM`. Crossref-verified 2026-09-13:
```latex
\bibitem{JM}
K.~Juschenko and N.~Monod,
\emph{Cantor systems, piecewise translations and simple amenable groups},
Ann. of Math. (2) \textbf{178} (2013), 775--787.
\doi{10.4007/annals.2013.178.2.7}.

\bibitem{Matui}
H.~Matui, \emph{Some remarks on topological full groups of Cantor minimal
systems}, Internat. J. Math. \textbf{17} (2006), 231--251.
\doi{10.1142/S0129167X06003448}.
```
Citation detail for the referee:
- Matui's Theorems 4.9 and 5.4 are stated for `D([[φ]]_0)`, and the remark after his Theorem 4.8 says "the commutator subgroup D([[φ]]_0) coincides with D([[φ]])".
- Juschenko–Monod state the same attribution: "see Theorem 4.9 in [Mat06] and the remark preceding it".

## Option 2: the same paragraph as an unnumbered subsection at the end of §1
(a) Current text, l.226-227:
```latex
side by arbitrary ring elements. Since $0\ne e_W\in I_N$ and $R$ is
simple, $I_N=R$. Thus $N=G$, completing the proof.\hfill$\square$
```
Replacement: the same two lines, followed by `\subsection*{The topological full group}` and the paragraph of Option 1, with `G` in place of `G_X` in the Whitehead sentence.

## (b) Complete proof text
The paragraph above is the complete proof. The identities it uses:
- Over `F_2`: `e_12(a)e_21(a^{-1})e_12(a)e_12(1)e_21(1)e_12(1) = diag(a,a^{-1})`, computed row by row. Over any ring the same holds with signs.
- `w_g w_h = w_{gh}`: on `{n_h = m} ∩ T^{−m}{n_g = n}`, `gh = T^{n+m}`, and `u^n e_A u^m e_B = u^{n+m} e_{T^{−m}A∩B}`.
- Injectivity: the coefficient of `u^0` in `w_g = Σ_n e_{g{n_g=n}}u^n` is `e_{{n_g=0}}`.

If a referee asks for more, add one display: `w_gw_h=w_{gh}` because `u^ne_Au^me_B=u^{n+m}e_{T^{-m}A\cap B}`.

## (c) Length
- About +11 source lines and +8 bibliography source lines.
- About +6 printed lines, plus two references.

## (d) Reader trade-off
- It adds a striking structural fact with a proof of two identities.
- The reader must trust two cited theorems: Matui (simple, f.g.) and Juschenko–Monod (amenable).
- The headline theorem does not get stronger.
- In my bounded check (Cairn grep, and the Matui and JM sources) I found no published question that it answers; sk-questions-oa/ggt may find one.
- Recommendation: include it if the note carries one short consequences paragraph (with expanders or other corollaries); otherwise keep it in Cairn only.

## Optional one sentence linking the finite models to the full group (not recommended without sk-citations)
- Under the finite models (l.131-144), `w_g` becomes the permutation matrix of `m ↦ m + n_g(T^m y)` on `Z/NZ` (part 1 §3). So the models of `G_X` extend periodic permutation models of `[[T]]`.
- Grigorchuk–Medynets prove LEF for `[[T]]` through Kakutani–Rokhlin towers (Theorem 2.6, per the pestov-9-1 write-up part 3). Whether "periodic approximation" is their mechanism in the note's sense is sk-citations' call.

## (e) Status
- Claim `topological-full-group-embeds-in-subshift-elementary-group` (route `-proof`): established, unreviewed.
- Firewall: the existing `whitehead-diagonal-map-is-not-multiplicative` (the "Whitehead homomorphism" `diag(θ(g), θ(g)^{-1}, 1)` fails for nonabelian images).
  - It now invalidates the false UN route and its two consumer routes.
  - The consumers are repaired for `N >= 4` through the LEF converse.
  - This concerns main's graph, not the note.
