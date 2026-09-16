# fpbs-benjamini-schramm-universal: special case / strengthening (swarm, 2026-09-16)

Agent: `hi-spec-fpbs-benjamini-schramm-univers`. Angle: find the best partial
results, then prove the conjecture for a new natural class or strengthen a known
partial result. Target: `fpbs-benjamini-schramm-universal`. Hole worked: the root
`fpbs-tree-projected-cayley-graphs-strict-thresholds`, specifically its bullet
"Still open: non-split groups". No lock was taken, because the result is recorded as
new nodes and no existing node was edited.

## 1. State of the art (sources checked 2026-09-16)

Classes with a nonuniqueness phase on **every** Cayley graph, or on the relevant
graphs:
* **Nonunimodular automorphism subgroup.** Hutchcroft arXiv:1711.02590v3
  Theorem 1.2 gives `p_c < p_u`, and arXiv:1804.10191 `thm:nonunimodular` gives
  `p_c < p_(q->q)`. Recorded in `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`
  and `fpbs-hyperbolic-nonunimodular-critical-l2-gap`. Timar, math/0702875, has
  earlier results on nonunimodular transitive graphs.
* **Hyperbolic graphs.** Hutchcroft arXiv:1804.10191.
* **Acylindrically hyperbolic groups, every Cayley graph.** Choi-Seo
  arXiv:2508.08932 (`fpbs-sc-choi-seo`).
* **Groups not of fixed price 1, every Cayley graph.** The Lyons implication, as
  recorded in the graph.
* **Products of a nonamenable and an infinite group.** Hutchcroft-Pan
  arXiv:2409.12283 Theorem 1.14, but only the weak conclusion
  `N_infinity(p_u) in {0, infinity}`.
* **Related recent work, none of which covers the class below:** arXiv:2412.15895
  and arXiv:2511.23317 (uniqueness thresholds on products); arXiv:2509.10631,
  arXiv:2502.02560, arXiv:1809.01284 (heavy clusters, weighted amenability);
  arXiv:2609.11845, arXiv:2609.07026 (the latest abstract search hits).

Within Cairn, tree-projected Cayley graphs of cyclic-by-free groups (the root) were
settled only in these cases:
* over `F_n x Z`, when one decoration set is symmetric up to translation
  (`fpbs-tree-projected-reversible-letter-nonunimodular`);
* over `F_n x Z`, when two decoration sets agree up to translation and reflection
  (`fpbs-tree-projected-letter-exchange-nonunimodular`);
* in large rank, `v + 2m sqrt(2n-1) < 2n-1`, for any cyclic kernel
  (`fpbs-tree-projected-large-rank-strict-thresholds`).

Rigid decorations over `F_n x Z` have discrete fibre-preserving automorphism groups
(`fpbs-tree-projected-rigid-decorations-discrete-automorphisms`). No source, arXiv or
Cairn, treated the non-central (twisted) groups `Z ⋊_chi F_n` in small rank.

Neither of the cited theorems at the level of groups reaches these groups. `H` is
an infinite amenable normal subgroup, so the group is not acylindrically hyperbolic
(standard, via Osin; not re-fetched), and it has fixed price 1 (Gaboriau; not
re-fetched).

## 2. What was proven (new)

**Claim `fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular`
(ESTABLISHED via `fpbs-twisted-cyclic-by-free-nonunimodular-proof`).** Let `Gamma`
have an infinite cyclic normal subgroup `H` that is **not central**, with
`Gamma/H ≅ F_n` and `n >= 2`. Then every tree-projected Cayley graph `X` of `Gamma`
has a closed nonunimodular automorphism subgroup with four orbits. Hence
`p_c(X) < p_(2->2)(X)` and `p_c(X) < p_u(X)`.
* The decoration sets are arbitrary, so rigid ones are included.
* The rank is arbitrary, so rank 2 is included.
* The claim settles the "non-split groups" bullet of the root. Every such extension
  splits; the groups meant are those other than `F_n x Z`, that is `chi ≠ 1`.

**How.**
1. *Normal form.* `Gamma ≅ Z ⋊_chi F_n`. Colour `g` by `chi(g)`, and orient
   `{g,gs}` out of `g` if `chi(g) = +1`, otherwise out of `gs`. Then the edges of
   `X` over it are exactly `(m,p)–(m+d,q)`, `d in D_s` (shape lemma).
2. *Local structure.* For a twisted letter (`chi(s) = -1`), both `s`-edges at a
   vertex point out (colour `+`) or both point in (colour `-`). So they carry the
   **same** oriented shape. Every automorphism of the tree preserving labels and
   orientations lifts to `(m,g) -> (m+k, phi g)`, with **no height potential**.
3. *Covering tree.* Take the covering tree of the four-vertex edge-indexed graph
   `A`:
   * `u, w` of colour `+` and `x, y` of colour `-`;
   * `s_0`-edges `u–x (2:1)`, `x–w (1:1)`, `w–y (1:2)`;
   * a 4-cycle `u–x–w–y–u` with indices `1:1` for every other twisted letter;
   * directed pairs `u <-> w`, `x <-> y` with indices `1:1` for untwisted letters.

   It is isomorphic to `Cay(F_n,B)` with its colours, labels and orientations. Its
   covering-map-preserving group `G_A` lifts to `L ≅ G_A x Z`, which is closed with
   four orbits. Along a walk from `y_0` over `u` to `y_1` over `u`, the stabilizer
   orbit sizes are `1` and `2`.

**Contrast, the new phenomenon.** Over `F_2 x Z`, the decoration data
`D_a = {0,1,3}`, `D_b = {0,1,4}`, `V = {±1}` give a Cayley graph whose whole
automorphism group is discrete. Over `Z ⋊ F_2` with `a` or `b` (or both) acting by
`-1`, the same data give a nonunimodular subgroup. The full group of colour-, label-
and orientation-preserving tree automorphisms is unimodular here too; only the finer
covering structure of `A` breaks unimodularity.

**Precise reduction of the root (new route
`fpbs-tree-projected-reduce-to-rigid-decorations`).** The root follows from four
claims:
* the twisted claim above;
* `fpbs-tree-projected-reversible-letter-nonunimodular`;
* `fpbs-tree-projected-letter-exchange-nonunimodular`;
* the new OPEN hole `fpbs-tree-projected-rigid-decorations-strict-thresholds`
  (rigid decorations over `F_n x Z`, arbitrary vertical part).

The case split is exhaustive: the `2n` oriented shapes `D_s`, `-D_s` either have a
coincidence up to translation, which is the reversible-letter or letter-exchange
case, or are rigid. So the rigid hole is now the exact open part of the root.

**Artifacts.**
* `research/artifacts/fpbs-twisted-cyclic-by-free-nonunimodular-2026-09-16.md`:
  full proof, remarks, and script output.
* `experiments/fpbs-twisted-cyclic-by-free-2026-09-16/twisted_lift_check.py`:
  checks the shape lemma from the group law, the local types of `Y` against `T`,
  the potential-free lift of random elements of `G_A` in six twisted cases (ranks 2
  and 3, rigid data included; 0 bad edges), the counts `1` and `2`, and a negative
  control on the `F_2 x Z` group law (248 bad of 1272 edges).

## 3. Approaches tried and where each dies

* **Twisting applied to `F_n x Z` (rigid case).** Over `F_n x Z` each letter has
  one incoming and one outgoing edge at every vertex, with shapes `D_s` and `-D_s`.
  Rigidity forbids matching them, so the new mechanism has nothing to exchange.
  The twisted group contains `Z x F_(2n-1)` with index 2, but its tree-projected
  Cayley graphs are not Cayley graphs of a direct product, and no transfer of
  thresholds is known.
* **Choosing a different nonunimodular structure on rigid `F_n x Z`.** It dies at
  `fpbs-tree-projected-rigid-decorations-discrete-automorphisms`: for `S_rig` the
  whole automorphism group is discrete.
* **Large-rank adjacency norm on rigid sets.** Rigid sets have `m >= 3`. The
  criterion needs `n >= 19` (with `v = 0`) or `n >= 21` (with `v = 2`), so rank 2 is
  out of reach.
* **Relative gap along amenable subgroups.** It dies at
  `fpbs-central-amenable-relative-threshold-is-pu`: the premise equals `p_c < p_u`.
* **Other classes considered before choosing the hole.**
  * For `B_3`, the centre is infinite cyclic and `B_3/Z ≅ PSL_2(Z) ≅ Z/2 * Z/3` is
    virtually free, not free. So `B_3` is not of the root's form, and the shape
    lemma has no free basis to act on. It was not pursued.
  * The averaged tilt, `research/artifacts/fpbs/docs/ps-averaged-tilt-relative-susceptibility.md`,
    is a recorded dead end.
* **Abelian coefficients.** `M ⋊_{±1} F_n` with `M` finitely generated abelian goes
  through verbatim. It is recorded only as a remark in the artifact, Section 9.2,
  not as a claim, because it adds no new difficulty.

## 4. Next steps

1. **Rigid hole.** The only open part of the root is
   `fpbs-tree-projected-rigid-decorations-strict-thresholds`. Any proof must work on
   unimodular graphs, for example `S_rig` with discrete `Aut`. Candidates:
   * the critical fibre-sphere bubble (`fpbs-tree-projected-sphere-bubble-l2-equivalence`);
   * a comparison between the rigid Cayley graph of `F_2 x Z` and a twisted Cayley
     graph with the same decoration data. The two graphs have the same local
     structure over each tree edge and differ only in how orientations are arranged
     along the tree. A monotone coupling or a threshold comparison between them would
     transfer `p_c < p_u`. This is untested.
2. **Beyond tree projection.** The shape lemma needs generators projecting to basis
   letters. For generating sets with longer projections, the twisted group still
   acts, but the lift condition becomes a condition on words. It is worth testing
   whether the four-vertex covering structure extends.
3. **Root text.** The root still lists "non-split groups" as open. That bullet is
   now settled by the twisted claim. The root was not edited, since it is a committed
   node from another agent.
