---
rg: 2
id: fpbs-word-chords-are-dominated-by-merges
kind: claim
title: Attaching k arcs with arbitrary labels to a folded graph and folding identifies its vertices exactly as at most k vertex merges do, so on every finite F(a,b)-set the relative chord number of K = <a, bab^-2> equals the 2-of-3 percolation number
distinct_from:
  fpbs-mal-bootstrap-certified-chords-pay-seed-floor: that charges chord firings of a local bootstrap rule set and shows no finite-range rule set is exact (bab and bbab); this is a global statement about the whole Stallings fold of a finite level, where every chord, of any length and in any circuit, is charged to at most one vertex merge.
  fpbs-mal-graphing-b-length-weighted-floor: that unfolds a chord of b-length |h| into |h| seeds and loses the factor |h|; this charges each chord one seed, with no length factor, on finite levels.
  fpbs-mal-profinite-fold-density-is-finite-percolation: that computes the fold seed density sigma_b of a profinite action from the percolation numbers r(Q_n) of its levels; this shows that r(Q) is also the least number of chords with arbitrary labels, which is what makes sigma_b equal to relative cost.
  fpbs-mal-fold-closure-exactness: that identifies generation by b-seeds with conull 2-of-3 closure on free actions; this is the finite-level statement for chords with arbitrary labels, proved by a folding potential rather than by closure rounds.
  fpbs-mal-modp-promotion-certificates-are-fox-annihilators: that is the H_1(-;F) lower bound k_u(V) on extra generating edges, which vanishes along towers; this is the exact value of the least number of extra edges, and it is linear in |Q| on expanders.
artifacts:
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/wordchords.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/pair_test.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/pair_n12_l5.txt
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/general_test.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/general_n2_out.txt
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/rho_vs_r.py
  - experiments/fpbs-word-chords-vs-merges-2026-09-17/rho_vs_r_out.txt
---

**ESTABLISHED** through `fpbs-word-chords-are-dominated-by-merges-proof`.

**Setting.**
- Labelled graphs have edges labelled `a` or `b`. Each edge can be read
  backwards, with the inverse label. A graph is *folded* when no vertex has
  two distinct edges with the same label, counting inverse readings.
- `fold(G)` is the Stallings fold of `G`.
- For a folded graph `Γ` and a set `P` of pairs of vertices, `cl_Γ(P)` is the
  least equivalence relation on `V(Γ)` that contains `P` and is *fold-closed*:
  if `u ~ v` and `u -l-> u'`, `v -l-> v'` are edges, then `u' ~ v'`.

**Claim.**

1. **(Domination lemma.)** Let `Γ` be a finite folded graph. Attach `k`
   paths `γ_1, …, γ_k` to `Γ`. Each path has any labels and runs between
   vertices of `Γ`. Let `H = fold(Γ ∪ γ_1 ∪ … ∪ γ_k)`, and let `R_H` be the
   relation "same vertex of `H`" on `V(Γ)`. Then `R_H = cl_Γ(P)` for a set `P`
   of at most `k` pairs. More precisely, `|P| ≤ k − (E_Δ − V_Δ)` and
   `E_Δ ≥ V_Δ`, where:
   - `V_Δ` counts the vertices of `H` that contain no vertex of `Γ`;
   - `E_Δ` counts the edges of `H` that contain no edge of `Γ`.

2. **(Structure of Γ_K over Q.)** Let `L = F(a, b)` act on the right on a
   finite set `Q`, with `n = |Q|`. Let `K = <a, c>`, where `c = b a b^{-2}`.
   Let `Γ_Q^K` be the fold of this graph:
   - real vertices `Q`;
   - an `a`-edge `p -> p·a` for each `p`;
   - a path labelled `c` from each `p` to `p·c`.

   Then `Γ_Q^K` has exactly three vertices `R_y, W_y, X_y` over every
   `y ∈ Q`, and `4n` edges:
   - `R_y -a-> R_{ya}`;
   - `R_y -b-> W_{yb}`;
   - `W_y -a-> X_{ya}`;
   - `W_y -b-> X_{yb}`.

3. **(Merges are seeds.)** The fold-closed relations on `V(Γ_Q^K)` that relate
   only vertices over the same point correspond bijectively to the subsets
   `S ⊆ Q` closed under the 2-of-3 rule on the triples
   `{y, y·a^{-1}, y·b^{-1}}`, counted with multiplicity. Under this
   correspondence:
   - `R_y ~ W_y` iff `y ∈ S`;
   - `R_y ~ X_y` iff `y·a^{-1} ∈ S`;
   - `W_y ~ X_y` iff `y·b^{-1} ∈ S`.

   Hence the least number `ρ(Q)` of merges that folds `Γ_Q^K` onto the
   Schreier graph of `Q` equals `r(Q)`. Here `r(Q)` is the least 2-of-3
   percolating set, for the triples `(y, g·y)` of the left action
   `g·y := y·g^{-1}`, which is the convention of
   [[fpbs-mal-profinite-fold-density-is-finite-percolation]].

4. **(Chords.)** Let `d(Q)` be the least number of chords `(p, w)`, with
   `p ∈ Q` and `w ∈ L` arbitrary, whose paths, attached from `p` to `p·w`
   and folded with `Γ_Q^K`, give a graph with exactly `n` vertices. Then

   ```text
   d(Q) = ρ(Q) = r(Q).
   ```

**Reading.** On a finite level, a word chord of any length, and any circuit
of chords, never does more than one vertex merge. By item 3, a vertex merge
is exactly one `b`-seed of the 2-of-3 closure. The `bab ⊔ bbab` obstruction
of [[fpbs-mal-bootstrap-certified-chords-pay-seed-floor]] concerns local
derivation rules and does not contradict this. Two chords there do the work
of two merges, and the charge is made by the global fold potential, not by a
local rule.

**Evidence.**
- `rho_vs_r.py` gives `ρ = r` on 48 of 48 random transitive `Q` with
  `n ≤ 9`.
- `pair_test.py` folds every pair of reduced arcs of length `≤ 5` sharing a
  port, over random `Q` with `n = 12`, about 1.35 million pairs per trial.
  It finds no pair whose induced relation needs 3 merges, and no pair
  reaching `n` vertices when `ρ = 3`.
- `general_test.py` repeats this with random folded base graphs.
