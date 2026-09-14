# sk-general-statement proposal: every finite field and every rank in the note

Lane sk-general-statement (ROSTER-H, wave 10), 2026-09-13.
- **Task:** the exact rev4 text for the most general verified form of Theorem 1: every finite field F_q, every n ≥ 2, finite models PSL_{nN}(F_q). Decision 74, option R3: at most about 12 proof lines naming the changes.
- **Base texts:**
  - the rev4 draft `sk/drafts/rev4.tex` (sk-editor-4, 742 lines, md5 eee41cb50790146c7b93d77beb794470), which already states n ≥ 2 over F_2 and has a "Rank two" subsection;
  - the landed rev3 (main 9047d0d3c9, md5 274f1936…), for the n ≥ 3 variant.
- No `.tex` file was edited.

## (a) Placement and current text

**rev4 draft.**
- Theorem 1, l.80–82, is unchanged:
  ```latex
  hyperlinear. For every $n\ge2$, $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$
  is also an infinite, finitely generated, simple Kazhdan LEF group, and
  for $n\ge3$ it is the limit of groups $\SL_{nN}(\F_2)$ in the same way.
  ```
- Insert the subsection below after l.283 (`LEF.\qed`, end of "Rank two") and before l.285 (`\subsection*{Brown's formulation}`).

**Landed rev3 (n ≥ 3 variant, if rank two is not adopted).**
- Insert after l.252 (`$K=G$.\qed`), before `\subsection*{Brown's formulation}`.
- In the first sentence replace `$n\ge2$` by `$n\ge3$`, and in the second sentence `for $n\ge3$ it is` by `it is`.

## (b) Verbatim LaTeX (20 source lines)

```latex
\subsection*{Other finite fields}
For a finite field $\F_q$ and $n\ge2$, the group
$G=\EL_n(\LC(X,\F_q)\rtimes_T\Z)$ has property~\textup{(T)}, its centre
$Z$ consists of scalar matrices, and $G/Z$ is an infinite, finitely
generated, simple LEF group; for $n\ge3$ it is the limit of groups
$\PSL_{nN}(\F_q)$ whose Cayley graphs form expanders. The proofs above
apply with $\F_q$ for $\F_2$, a generator of $\F_q$ added to $u^{\pm1}$
and the $e_a$, and three changes. First, as a nonconstant unit of
$\LC(X,\F_q)$ commutes with every $e_{ij}(e_V)$, take $g\in K\setminus Z$
and the roots $e_{ij}(e_V)$ and $e_{ij}(e_Vu)$: if $g$ commutes with all
of them, then $g=cI_n$ with $cu=uc$, so $g\in Z$. Second, define small
sets and the $\epsilon_{ab}$ with $w+1$ in place of $w$. Then
$k-I_n=(ghg^{-1}-h)h^{-1}\in M_n(S)$ has vanishing columns at the top
level, so $k\in H\cong\GL_d(\F_q)$ is not scalar. If $K$ met the copy of
$\SL_d(\F_q)$ only in central elements, $\sigma\mapsto[k,\sigma]$ would be
a homomorphism from this perfect group to its centre, so $k$ would
centralize it and be scalar. So $K$ contains this quasisimple group.
Third, for every $\lambda$ and all large $\ell$, a word of length at most
$\lambda$ is central in $G$ exactly when its image in
$\SL_{nN_\ell}(\F_q)$ is scalar.
```

**Compile** (MSI texlive/2025, pdflatex ×3). Paths are in `/scratch.global/sauer354/sk/sk-general-statement/`, and the inputs are `coderepo.tex` from main plus the draft.
- Base `rev4-base.tex` (md5 eee41cb5…): 0 errors, 0 overfull, 0 undefined, 8 pages.
- With the subsection, `rev4-fq.tex` (763 lines, md5 47bf8f27a604e051df476ab3ffbf9252): 0 errors, 0 overfull, 0 undefined, 8 pages.
- `\PSL` is already defined in the draft. No new bibitem.

## (c) Length
+20 source lines, and the page count stays at 8. The statement takes 5 lines, and naming the changes takes 14.

## (d) Reader-facing trade-off
The theorem stops depending on the arbitrary choice of F_2 and holds for every finite field and every rank. That costs 20 lines and no new citation; the only new fact the reader must trust is that SL_d(F_q) is perfect with simple central quotient, which is classical. Theorem 1 keeps its clean binary headline, where the group itself is simple.

## (e) Status of every claim in the text

| claim in the subsection | Cairn node | review |
|---|---|---|
| (T), scalar centre, simplicity mod centre, LEF, n = 2, every q | `subshift-el-2-simple-modulo-centre-every-finite-field` (sk-el2-fq, fa92d5adcb) | PASS (sk-verify-8 part2 §4); PASS-WITH-FIXES F4/F5 (sk-verify-12). The text obeys both: no expander clause for n = 2, and Z only as a set of scalar matrices |
| (T) in rank two | `complementary-full-idempotents-make-el-2-kazhdan` | PASS (sk-verify-4 part5 §5) |
| simplicity mod centre, n = 3, every q | `subshift-elementary-group-is-simple-modulo-centre` | PASS (ex-review-groups part1), by the ring route |
| the tower route over F_q (nonscalar commutator at an extreme level) | `root-localization-commutator-is-never-scalar`; sk-el2-fq artifact §3 steps 1–3 and §5 (n ≥ 3 bullet) | PASS (sk-review-1 part4 §1); steps 1–3 PASS (sk-verify-8, sk-verify-12) |
| marked limit of PSL_{3N}(F_q), expanders | `finite-simple-groups-converge-to-simple-kazhdan-group` (+ `-proof`) | GAP corrected forward (ex-review-groups part8 §8.6, part11); convergence step PASS (sk-review-2 part2) |
| (T) of EL_3 over the free F_q-algebra | EJZ Thm 1.1; `elementary-group-property-t-over-free-algebras` | cited; established |
| this LaTeX, and the n ≥ 3 and PSL_{nN} generalisation | proposal only | unreviewed; queued with sk-verify-13 |

## (f) Derivation checks run for this text
Each item below was re-derived by this lane against the rev4 draft's notation (l.201–283).

1. **Generators.** Over F_q, u^{±1} and the e_a generate only an F_p-algebra. Adding λ with F_p[λ] = F_q gives R, and e_ij(λ) joins the generators of G and of EL_n(F). This matches the marking note in `finite-simple-groups-converge-to-simple-kazhdan-group`.
2. **Step 1.**
   - rev4 l.210–222 give g = cI_n with c ∈ LC(X,F_q) from commuting with all e_ij(e_V), V small. Over F_q, "equals 1 on U" becomes "is a nonzero constant on U".
   - Commuting with e_ij(e_Vu) gives c e_V u = e_V u c = e_V (c∘T^{-1}) u, so c = c∘T^{-1} on every small V, hence everywhere, so cu = uc.
   - Then cI_n commutes with every e_ij(r), so g ∈ Z. No constancy argument is needed.
3. **Margin.** With small sets and ε_ab for m = w+1 (while w still bounds the exponents of g^{±1}), (fu^a)(e_Vu^c)(f′u^b) = f e_{T^aV}(f′∘T^{−a−c})u^{a+c+b} ∈ F_q ε_{a,−(c+b)}, with second index in [−m, w].
   - k − I_n = ghg^{-1}h^{-1} − hh^{-1} = (ghg^{-1} − h)h^{-1}, and h^{-1} = I − ε_{0,−c}E_ij, so the second indices stay in [−m, w].
   - k^{-1} − I_n = h(gh^{-1}g^{-1} − h^{-1}) also lies in M_n(S), so k ∈ H as in rev4 l.246–247.
   - The columns (p, m) of k − I_n vanish, so a scalar κ = λI would force λ = 1 and k = 1, against k ≠ 1.
4. **Quasisimple step.**
   - [k,σ] ∈ K, since K is normal and σ ∈ G.
   - [k,σ] ∈ S, since S = image of SL_d(F_q) is normal in H and k ∈ H.
   - If K ∩ S ⊆ Z(S), then [k,στ] = [k,σ]·σ[k,τ]σ^{-1} = [k,σ][k,τ]. So σ ↦ [k,σ] is a homomorphism from the perfect group SL_d(F_q) (d ≥ 3) to an abelian group, hence trivial. So κ centralizes SL_d(F_q) and is scalar: a contradiction.
   - A noncentral normal subgroup of a quasisimple group is the whole group. So S ⊆ K, e_pq(e_V) ∈ K, and the level steps are unchanged: rev4 l.252–258 for n ≥ 3, and the sign-free Peirce propagation of l.276–281 for n = 2.
   - So every normal K ⊄ Z equals G, and G/Z is simple.
5. **Centre.** The central g commute with every e_ij(e_V) and e_ij(e_Vu), so Z ⊆ F_q^× I_n by item 2. Scalar matrices in G are central. The subsection claims only "consists of scalar matrices", in line with F5.
6. **Marked limit.**
   - Z is finite and each w ∈ Z is λI with λ ∈ F_q^×. For the finitely many words of length ≤ λ and finitely many λ, the entries of w − λI are nonzero in R iff their ρ_ℓ-images are nonzero, for large ℓ (rev4 l.170–191, field-independent).
   - So w ∈ Z iff ρ_ℓ(w) is scalar, iff ρ_ℓ(w) ∈ Z(SL_{nN_ℓ}(F_q)).
   - So G/Z is the marked limit of PSL_{nN_ℓ}(F_q), which is simple for nN_ℓ ≥ 3. Both G and G/Z are LEF.
7. **Expanders.**
   - For n ≥ 3, the Cayley graphs of SL_{nN_ℓ}(F_q) on the images of the fixed generators have a uniform spectral gap, by (T) of EL_n(F) over F_q (EJZ). A function on the PSL quotient pulls back to one on SL with the same Rayleigh quotient, so the gap passes to the quotients.
   - For n = 2 no expander claim is made, since EL_2 over a free algebra lacks (T).

## Firewalls respected
- Decision 23: the text never says "with the same proof". It names the roots e_ij(e_Vu), the margin with the nonscalar commutator, and the scalar marking.
- The expander clause is claimed for n ≥ 3 only (sk-verify-12 F4).
- "n = 2 loses (T)" is never written.
- The centre is stated as a set of scalar matrices, not all of F_q^×I (F5).

## Option 0
No change: the note stays over F_2. The general statement stays in Cairn through the nodes in (e).
