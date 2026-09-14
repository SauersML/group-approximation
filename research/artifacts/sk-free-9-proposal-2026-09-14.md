# sk-free-9 proposal: the simple limits of the finite models are exactly the G_X (2026-09-14)

Target: `simple_kazhdan_sofic_group.tex` rev4.3 (main 696c4b602e, md5 0648e5f876e467e21ebf475e08b8ee92). Line numbers refer to that file.

## P1 (recommended): a converse to Theorem 1, +6 printed lines

**Placement.** In §4 (`sec:wp`), right after `\end{proof}` of `cor:wp` (l.535) and before "For derived topological full groups, Grigorchuk and Medynets proved …" (l.537). The criterion it uses (triviality through the tables on the language) is proved at l.507–514 of that proof, and the models it uses are those of §2 (l.249–271).

**Verbatim LaTeX:**
```latex
The same criterion describes every limit of the finite models of
Section~\ref{sec:main}. Mark $\SL_{3N}(\F_2)$ as there, with a periodic
sequence $y$ of least period $N$ in place of $y_\ell$. If these marked groups
converge as $N\to\infty$, then for each $\lambda$ the words of length
$2\lambda+1$ of $y$ stabilize, and the limit is $G_Y$ for the subshift $Y$
with these words, which is infinite. A proper closed invariant subset of $Y$
gives a proper nonzero ideal of $\LC(Y,\F_2)\rtimes\Z$, whose level subgroup
is a proper normal subgroup. So the simple limits of these finite simple
groups are exactly the groups $G_X$ of Theorem~\ref{thm:main}.
```
About 600 characters, 6 printed lines at the note's measure. No new bibitem.

**Trade-off (reader merit).** It makes the title canonical. G_X is not merely some Kazhdan limit of SL_{3N}(F_2): among all limits of the paper's own finite simple models, the simple ones are exactly the G_X. The reader has to trust nothing new; every step reuses §2 and §4.

## Derivation check (every step)
1. **Well-defined models.** D_y(e_a)δ_t = e_a(T^t y)δ_t needs only coordinate 0, so any periodic y gives the marking {e_ij(I), e_ij(P^{±1}), e_ij(D_y(e_a))} used in §2 (φ_ℓ(S) with S = {1,u,u^{-1}} ∪ {e_a}).
2. **Triviality depends only on windows.**
   - A word of length ≤ λ in these generators has entries Σ_j D_y(f_j)P^j with each f_j depending on coordinates in [−λ,λ], by the product rule PD(f)P^{-1} = D(f∘T^{-1}) (l.264) and the degree count in §1, "Finite simple models".
   - For N > 2λ+1 there is no aliasing in P^j (|j| ≤ λ), so the word is trivial iff every table f_j − δ_{j0}δ_{pq} vanishes on all cyclic windows of y of length 2λ+1.
   - That is the note's §4 criterion with L(X) replaced by the window set W_λ(y).
3. **Convergence ⇔ stabilization.**
   - (⇐) If W_λ(y) is eventually constant, triviality of words of length ≤ λ is eventually constant.
   - (⇒) The word for e_12(∏_{t<m} u^{-t}e_{v_t}u^t) has length O(m) and is trivial iff v ∉ W(y) (the argument of §4, l.512–514), so convergence forces each W_λ(y) to be eventually constant.
4. **The limit is G_Y.**
   - The limit window sets L = ∪_λ lim W_λ form a factorial language, and every word in L extends on both sides within L, since windows of periodic words extend. So a subshift Y with L(Y) = L exists.
   - By §4 (a word is trivial in G_Y iff its tables vanish on L(Y)), the marked limit equals G_Y with the marking e_ij(s), s ∈ S.
5. **Y is infinite.** If Y were finite, say p-periodic, then for λ ≥ p every (2λ+1)-window of y would be a window of the periodic point, forcing y to have period p. That contradicts N → ∞.
6. **Not minimal ⇒ not simple.**
   - Let ∅ ≠ Z ⊊ Y be closed and invariant, and let I be the set of Σ f_j u^j with every f_j vanishing on Z.
   - I is a two-sided ideal (Z is invariant). It is nonzero: Y∖Z is open and nonempty, so it contains a cylinder set U ∩ Y with U ∩ Z = ∅, and e_U ∈ I. It is proper: 1 ∉ I since Z ≠ ∅.
   - The kernel of EL_3(R_Y) → EL_3(R_Y/I) contains e_12(e_U) ≠ 1 and misses e_12(1), whose image e_12(1̄) ≠ 1 since R_Y/I ≅ LC(Z,F_2)⋊Z ≠ 0. So it is a proper nontrivial normal subgroup.
7. **Minimal ⇒ simple and attained.** Theorem 1 gives simplicity, and its proof exhibits G_X as such a limit (y = y_ℓ). So the simple limits are exactly the G_X of Theorem 1.

## Model tests
- **y_k = 0^k1^k (least period 2k).**
  - Limit language: all words 0^a1^b and 1^a0^b, plus the constants. Y contains the fixed points 0^∞ and 1^∞, so it is not minimal.
  - Ideal: functions vanishing on {0^∞}, giving a proper normal subgroup. Consistent.
- **y_ℓ from a Sturmian X (§2).** Y = X minimal, G_X simple. Consistent.
- **y_k containing every binary word of length k (de Bruijn cycles, least period 2^k).** Y is the full shift, not minimal, not simple. Consistent.
- **Bounded least periods.** No convergence to an infinite group; excluded by N → ∞.

## Status of inputs
- `generic-limit-of-subshift-sl-models-is-simple-kazhdan` (sk-free-2): its statement contains P1 (the closure of the periodic-word models is the isolated points ∪ {G_Y : Y infinite chain transitive}, and the simple ones are exactly the G_X with X infinite minimal). Reviews: sk-verify-15 PASS (part3 §4), sk-verify-16 PASS (§7).
- `subshift-algebra-groups-embed-in-marked-groups`: PASS by sk-verify-3 (part4 §1); Y ↦ G_Y is a homeomorphism onto a closed set.
- Main's own check: steps 1–7 above re-derived in this lane.
- UNREVIEWED: the LaTeX as note text (queued).
- Novelty: specific to the note's models; no prior statement is expected. Bounded to a grep of main (the boundary theorem is recorded in `research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md` §§3–4, from the ex swarm).

## P2 (optional, secondary): marking-free expanders, +2 lines, +1 bibitem
After Theorem 1's expander clause, or in §1 after "form a family of expanders":
```latex
In fact every sequence of finite groups converging to $G$ in the space of
marked groups eventually forms expanders, as $G$ is a quotient of a finitely
presented Kazhdan group~\cite[Theorem~6.7]{Shalom}.
```
- **Input:** `kazhdan-marked-limits-eventually-uniform-expanders` (sk-verify-14 PASS; openness import checked through Stalder arXiv:0803.2592 l.158–160).
- **Caution:** the theorem number in Shalom, Invent. Math. 141 (2000) 1–54, still needs a source check before printing. Put it in only with a verified locator.
- **Trade-off:** it is stronger, but general, and it dilutes the explicit expander clause. Main's call.
