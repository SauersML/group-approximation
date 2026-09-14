---
rg: 2
id: crossing-pair-two-cycle-lot-li-proof
kind: route
title: Eliminate one vertex of the crossing pair, compute every multiset of minima exactly, and peel the forest around the one four-letter multiset
target: crossing-pair-two-cycle-lot-groups-are-locally-indicable
requires:
  - barreto-minian-concatenable-minima-give-local-indicability
  - locally-indicable-2-complex-with-h2-zero-is-aspherical
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
  - experiments/lot-torsion/crossing_pair_check.py
  - experiments/lot-torsion/crossing_pair_check-run.log
---

**Standard inputs used without a node.**
- Eliminating a generator that occurs exactly once in a relator (solve for it, substitute, delete
  both) is a Tietze transformation. It keeps the group and the deficiency.
- `P(Γ)` has deficiency `1` and `H_1(G(Γ)) = Z` (quoted in `barreto-minian-concatenable-minima-citation`).
- For a multigraph, contracting a non-loop edge keeps `#edges - #vertices + #components`, and
  deleting a loop lowers it by one.
- **I-values.** Barreto--Minian, Remark after Definition 2.14, verbatim: "Given a relator $r$, the
  multiset of letters in which the minima of the sequence of $I$-values of $r$ are attained is exactly
  $m_{\varphi}(r)$." With weight `1` on every generator, a positive letter's I-value is the total
  exponent of the preceding initial subword, and a negative letter's is that of the initial subword
  ending with it.

**Step 1: the elimination.** Put `t = t_e`. The relator `r_e = v u t^-1 u^-1` contains `v` once, so
`v = u t u^-1`. Substituting into every other relator gives a presentation `P'` of `G(Γ)`:
- generators `V - {v}`, relators `r'_g` for `g ≠ e`;
- deficiency `1`, `H_1 = Z`;
- every relator has total exponent `0`, because `u t u^-1` has exponent sum `1`.

**Step 2: exact multisets of minima.** Fix `g ≠ e` and write `i = i(g)`, `λ = λ(g)`, `t' = t(g)`. Since
`i ≠ t'` and `λ ∉ {i, t'}`, the vertex `v` has at most one role in `g`. The words below are
cyclically reduced; each possible cancellation is ruled out in brackets.

- **(A) `v ∉ {i, λ, t'}`.** `r'_g = r_g`, and `m = {i, λ}` (the LOT relator minima quoted in the citation route).
- **(B) `i = v`.** `r'_g = u t u^-1 λ t'^-1 λ^-1`, with I-values `0,1,1,1,1,0`, so `m = {u, λ}`.
  - [`u^-1 λ`, and cyclically `λ^-1 … u`, would need `λ = u`. Then `e` and `g` both point away from `v`
    with label `u`, contradicting interior reducedness.]
  - [`t u^-1` needs `t = u`, contradicting compression of `e`. `λ t'^-1` needs `λ = t'`, contradicting
    compression of `g`.]
- **(C) `λ = v`, `i ≠ u`, `t' ≠ u`.** `r'_g = i u t u^-1 t'^-1 u t^-1 u^-1`, with I-values
  `0,1,2,2,1,1,1,0`, so `m = {i, u}`.
- **(C′) `λ = v`, `t' = u`.** Cancelling `u^-1 u` gives `r'_g = i u t u^-1 t^-1 u^-1`, with I-values
  `0,1,2,2,1,0`, so `m = {i, u}`.
- **(C″) `λ = v`, `i = u`.** Cyclic cancellation of the outer `u … u^-1` gives
  `r'_g = u t u^-1 t'^-1 u t^-1`, with I-values `0,1,1,0,0,0`, so `m = {u, u, t', t}`.
  - [In (C)--(C″), `t u^-1` and `u t^-1` need `t = u`, which is excluded. `t'^-1 u` needs `t' = u`: that
    is (C′), and it is impossible in (C″) because `t' ≠ i = u`.]
  - [The cyclic pair `u^-1 … i` needs `i = u`: that is (C″). After it, the cyclic pair `t^-1 … u` needs
    `t = u`, which is excluded.]
- **(D) `t' = v`.** `r'_g = i λ u t^-1 u^-1 λ^-1`, with I-values `0,1,2,2,1,0`, so `m = {i, λ}`.
  - [`u t^-1` needs `t = u`, and the cyclic pair `λ^-1 … i` needs `i = λ`; both are excluded.]

**Step 3: the hypergraph of minima.** In cases (A), (B), (C), (C′) and (D), `m(r'_g)` is the left edge
`{i(g), λ(g)}` with `v` renamed `u`. Case (C″) is `i(g) = u`, `λ(g) = v`, which is the crossing partner
`f`.
- **`f` is the only such edge.** Two such edges would both point away from `u` with label `v`.
- **No renamed edge is a loop.** Such a loop comes from a left edge `{u, v}`, that is `(i, λ) = (v, u)`
  (excluded in (B)) or `(i, λ) = (u, v)` (the edge `f`).

So the multisets are the edges of `T_1 = (T(Γ) / e) - f`, as 2-element sets, together with
`Q = {u, u, t_e, t_f}` for `f`. Omitting the relator of `s` leaves the edges of `F = T_1 - s` and `Q`.

**Step 4: cyclomatic numbers.** Contracting the left edge of `e` keeps the cyclomatic number `2`, and
deleting the loop coming from `f` lowers it to `1`. So `T_1` has exactly one cycle, and removing an
edge `s` of that cycle gives a forest `F`.

**Step 5: concatenation.** Suppose the component `C` of `t_e` in `F` contains neither `u` nor `t_f` (the
other case swaps `t_e` and `t_f`). Order the sets as follows.
1. **Other components.** For every component of `F` other than `C`, take its edges growing a tree from a
   root. The first edge brings two uncovered vertices, and each later edge brings one.
2. **Then `Q`.** Its element `t_e` has multiplicity `1`, because `t_e ≠ t_f` and `t_e ≠ u` (compression
   of `e`). It is uncovered, since `t_e ∈ C` and nothing in `C` has been used.
3. **Then the edges of `C`,** growing from `t_e` outward. The earlier sets meet `C` only in `t_e`: they lie
   in other components or equal `Q`, and `u, t_f ∉ C`. So each such edge brings an uncovered vertex of
   `C`, and that vertex has multiplicity `1` in the edge.

This is a concatenation of all multisets but `m(r'_s)`.

**Step 6: conclusion.**
- `P'` has `n - 1 = k + 2` generators and `n - 2 = k + 1` relators, which are cyclically reduced with
  total exponent `0`. By Step 5 and `barreto-minian-concatenable-minima-give-local-indicability`, `G(Γ)`
  is locally indicable.
- A locally indicable group is torsion-free.
- `H_2(K(Γ)) = 0`, as computed in `locally-indicable-2-complex-with-h2-zero-is-aspherical`, so `K(Γ)` is
  aspherical.

**Mirror form.** Under `x ↦ x^-1`, the relator `i λ t^-1 λ^-1` becomes `i^-1 λ^-1 t λ`, which is a cyclic
permutation of the relator of the reversed edge `(t, λ, i)`. So `G(Γ) ≅ G(Γ^rev)`. `Γ^rev` is compressed
and interior reduced exactly when `Γ` is, and `T(Γ^rev) = I(Γ)`.

**Model test.** `experiments/lot-torsion/crossing_pair_check.py` reruns Steps 2--5 on 16902 instances
through the census code on main (`lot4.eliminate`, `lot2.minima`, `lot2.concat_order`,
`lot2.test_bm25`). It covers every crossing pair and every omitted relator of the sampled LOTs. There
were 0 minima mismatches and 0 disagreements between the Step 5 criterion and the computed
concatenability. The run log is in the artifact list.
