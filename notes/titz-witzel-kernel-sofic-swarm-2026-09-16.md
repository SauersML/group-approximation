# titz-witzel-kernel-sofic: swarm notes, 2026-09-16

Agent `swarm-titz-witzel-kernel-sofic`. The target claim was locked for the session and was not
edited. Outcome: **partial progress.** A new quantitative necessary condition on marked almost
actions of Radu's lattice is proved, and three obstructions are recorded. Soficity of `K` stays
open.

## Setup

* **The kernel.** `K = Γ_1^2` (arXiv:2509.05054v2) is simple, Kazhdan, torsion-free, finitely
  presented and not residually finite. Being simple, it is sofic iff one nontrivial element
  survives macroscopically in some almost action (`titz-witzel-soficity-is-one-finite-csp`).
* **Radu's lattice.** `Γ_R = <a,b,c,x,y,z | involutions, axax, ayay, azbz, bxbx, bycy, cxcz>`
  embeds in `K` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`). So `titz-witzel-kernel-sofic`
  forces `radu-bmw-lattice-sofic`, and a proof of nonsoficity may run through `Γ_R`.
* **The mark.** `δ = xz`. `δ^4` lies in the finite residual (Radu, arXiv:1712.01091,
  Proposition `33nonrf`). It is bounded by one commutator (`radu-mark-is-controlled-by-one-commutator`),
  and an exact quotient keeps it only if its kernel meets no vertex stabilizer of `T_v`
  (`radu-mark-survives-only-if-horizontal-group-embeds`).
* **Notation.** `C = <a,b,c>`, `V = <x,y,z>`, vertical tree `T_v = Γ_R/C`, local action
  `χ(h) = (−1)^(#c)`, `u = yδ^2y`.

## Literature gate (arXiv API and abstract pages, fetched 2026-09-16)

No source resolves soficity of `K`, of `Γ_R`, or of any non-residually-finite Kazhdan lattice in
a Euclidean building. Checked:

* **Primary sources.**
  * T. Titz Mite, S. Witzel, arXiv:2509.05054v2 (v2 2026-08-20). The kernel, Proposition 3.4,
    Lemma 3.5, and the Radu subcomplex.
  * N. Radu, arXiv:1712.01091, "New simple lattices in products of trees and their
    projections". TeX source read; Proposition `33nonrf` (the mark lies in every finite-index
    normal subgroup) and §5.
  * T. Titz Mite, S. Witzel, arXiv:2310.03662 (the earlier single example, already cited in
    `titz-witzel-cat0-lattices-citation`; not re-read).
* **Building lattices.** J. Lécureux, S. Witzel, arXiv:2605.06163v1 (2026-05-07), "The Normal
  Subgroup Theorem for lattices on two-dimensional Euclidean buildings". Normal subgroup and
  factor theorems. No invariant random subgroup or Stuck–Zimmer rigidity was stated in the
  abstract.
* **Soficity and stability.**
  * G. Kun, A. Thom, arXiv:2608.06222v3 (2026-08-06, v3 2026-08-20), "Nonsofic wreath products
    of residually finite groups". This refutes general amenable-by-sofic permanence, as already
    recorded in `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`.
  * V. Alekseev, A. Thom, arXiv:2608.05362v1 (2026-08-05), "Centralizers of sofic
    approximations of Kazhdan groups".
  * V. Alekseev, A. Thom, arXiv:2512.15494v1 (2025-12-17), "Remarks on approximability and
    stability for groups".
  * F. Fournier-Facio, arXiv:2608.02025v2 (2026-08-03, v2 2026-08-14), "A torsion-free
    non-sofic group".
  * P. Moravec, arXiv:2608.21817v1 (2026-08-22), "Polynomial permutation stability, soficity,
    and universal polynomial groups".
  * H. Ishikura, arXiv:2606.08279v1 (2026-06-06), "Tracks on planar complexes and soficity".
  * K. Ersoy, arXiv:2604.19174v4 (2026-04-21, v4 2026-06-08), "On minimal non-sofic and
    ω-non-sofic groups".
  * Z. Liu, arXiv:2608.29599v1 (2026-08-30), "Poisson actions of noncompact locally compact
    sofic groups have completely positive entropy".

For the 2025–2026 items only titles and abstracts were read, except arXiv:2509.05054, which
was read through the repository's citation nodes and artifacts. Their bodies were not searched
for a treatment of these lattices. One further query hit, arXiv:2605.09493, had no recovered
title and is unverified and unused.

## What was established

New claim `radu-mark-is-bounded-by-every-vertical-elliptic-element`, with route
`...-proof`, status computed from its requirements. Let `a,...,z` be involutions in a group with
a bi-invariant metric, with square defects at most `ε`. Let `γ` be a reduced word of length `L`
in `a,b,c`, with fixing radius `r` on `T_v`. Then

```text
d(δ^4,1) <= 4 d(γ,1) + (4L(r+4) + 48) ε.
```

At zero defect this becomes `d(π(δ^4),1) <= 4 d(π(g),1)` for every nontrivial vertically elliptic
`g`. The mechanism is Radu's finite step with metric bookkeeping.
1. Push `γ` to a boundary vertex `v·o` of its fixed ball. This gives `k ∈ C` with
   `d(k,δ) <= d(γ,1) + L(r+1)ε`.
2. Adjust `k` by `b` so that the sign character `χ_u` is trivial.
3. Then `k'` commutes with `u` up to `6(L+1)ε`.
4. Finish with `(RL1)`/`(RL3)`.

Radius facts:
* `r = 0` iff `#c` is odd, and `r = 1` iff `#c` is even and `#b` is odd.
* `r = 2` for odd `L` otherwise, so `r <= 2` for every odd `L`.
* In general `r <= 3N_+(L)+1 <= 9·2^L`, by pigeonhole on the section automaton.
* Observed for `L <= 17`: `r <= max(2, L−1)`.

Consequences:
* (C1) Under a kept mark `m`, every fixed nontrivial elliptic element has `liminf` support at
  least `m/4`.
* (C2) Weighted girth. A marked solution has no relation among `a,b,c` of cost below `m/ε`. In
  particular it has no odd relation of length below `m/(24ε) − 2`.
* (C3) In a metric ultraproduct representation keeping the mark, the images of vertex stabilizers
  are uniformly discrete, hence closed.

Data: experiments/titz-witzel-kernel-sofic-2026-09-16/elliptic_support_check.py and its output
(`ALL_OK`; exact normal-form checks for all reduced `γ` with `L <= 17`, plus 120 perturbed
permutation actions).

## Approaches tried and where each dies

1. **Elementary permanence.** Dead before this session (`titz-witzel-kernel-not-elementary-sofic`).
2. **Metric version of Radu's finite step.** Works: the claim above.
3. **Use the bound to collapse the mark in finite models.** Dies. In an almost action on `n`
   points, `C → Sym(n)` is an exact homomorphism with finite image, so killed words `γ_n` exist.
   * Pigeonhole bounds only `L_n <= 2⌈log_2 |C_n|⌉ + 2`, which can be of order `n log n`.
   * The proved radius bound is exponential in `L_n`.
   * A nonzero defect is at least `1/n`.

   So the cost `L_n(r_n+4)ε_n` is not controlled. What is needed is a *short, low-radius*
   relation among `a_n,b_n,c_n`. Nothing in the gate forces one, and (C2) says a marked
   solution must avoid them.
4. **Metric analogue of Caprace's inclusion** (the closure step of Radu's Proposition 5.1
   discussed in `radu-commutator-collapse`). Dies at (C3). In any ultraproduct representation
   keeping the mark, the closures of the images of vertex stabilizers are the images themselves,
   and they are discrete. A replacement for "infinite projection of a finite-index subgroup" has
   to come from elsewhere.
5. **Negative horn via unconditional elliptic collapse.** False (calibration K2). Pulling back
   finite quotients of the residually finite `Q = Γ_R/Λ_v` gives exact actions where the mark
   is trivial but every fixed elliptic element acts freely. Any collapse argument must use the
   mark hypothesis.
6. **Horizontal analogue** (bound the mark by `T_h`-elliptic supports). False (calibration K1).
   `[δ^2, yδ^2y]` is a reduced `V`-word of length 20 in `Λ_v`. It dies in
   `Γ_R/γ_2(Λ_v)`, which keeps the mark.
7. **Invariant random subgroups.** The limiting stabilizer IRS of a marked almost action
   satisfies `P(g ∈ Stab) <= 1 − m/4` for every nontrivial vertically elliptic `g`, by (C1).
   Deriving a contradiction would need IRS rigidity for `Γ_R` or `K`. Lécureux–Witzel prove
   normal subgroup and factor theorems only, and no IRS statement was found. Not pursued.
8. **Amenable-by-sofic permanence** for the groups `G_k` of
   `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`. General permanence is refuted by
   Kun–Thom. The finite-kernel case is open but does not cover `G_k`, whose kernels are infinite
   free nilpotent. No progress.
9. **Random numerics.** Perturbing exact actions of the abelianization gives marks of at most
   `0.085`. These are sanity checks of the inequality only, not evidence for or against
   soficity.

## What remains open

* `titz-witzel-kernel-sofic`, `radu-bmw-lattice-sofic` and `radu-commutator-collapse` are
  unchanged.
* **Polynomial radius bound.** Prove `r(γ) <= max(2, L−1)`, or any polynomial bound. Then (C2)
  becomes a polynomial girth condition, and item 3 above would need only
  `polylog(|C_n|)·ε_n → 0`.
* **Positive horn search.** Marked solutions must make `<a_n,b_n,c_n>` have large weighted girth.
  Candidate constructions should start from high-girth actions of `C_2 * C_2 * C_2` and fit
  `x,y,z` to the squares, rather than from actions of `C` with short relations. Not checked
  here: whether the structured ansatzes killed in the `titz-witzel-*` nodes (which live in the
  two-generator building gate, not in `Γ_R`) induce short relations among `a,b,c`. If they do,
  (C2) would explain those failures uniformly.
* **Negative horn.** A proof must exploit the mark to produce a low-cost elliptic relation, or
  bypass elliptic elements altogether (K2).

## Referee (2026-09-16)

Adversarial referee pass on `radu-mark-is-bounded-by-every-vertical-elliptic-element` and its
route `...-proof`, the artifact script and output, and these notes.

**What was checked.**

* **Square table and defects.** Re-derived all nine moves `hs -> s'h'` from the six relators,
  and checked that each `s h s' h'` is a cyclic rotation of the listed relator or its inverse, so
  each move costs exactly the listed defect.
* **Sections and Lemma R.** Checked by hand. The solver's stated weak point (that pushing `γ`
  through `v` returns the word `v` literally) is proved in general, not only for `L <= 17`.
  * `γ v = v' k` in `Γ_R` and `γ` fixes `vo`, so `v'C = vC`, hence `v' = v` in `V`, since `V` is
    simply transitive on the vertices of `T_v`.
  * A word of length `|v|` in `C_2 * C_2 * C_2` that equals the reduced word `v` is `v` itself.
  * Lemma R (the minimizer is empty or ends in `y`) follows from the local action, as written.
* **Steps 1–5 of (EB1).** Checked line by line.
  * Replayed the three move sequences for `λ_a`, `λ_c`, `λ_b` letter by letter. The sign
    induction (`b ↦ u^(−1)`), Step 4, and the arithmetic
    `2(2d + 6(L+1)ε) + 4L(r+1)ε + 36ε = 4d + (4L(r+4)+48)ε` are correct.
  * The constants 16 and 36 are the coefficient sums of `(RL1)` and `(RL3)` in the committed
    `radu-mark-is-controlled-by-one-commutator`.
* **Fixing-radius facts.**
  * 4(a) checked by hand: the `x`/`z` push swaps `a ↔ b` on exactly one side, so the counts of
    `b` add up to `#a + #b`.
  * 4(b) checked by hand: a repeated pair `(h_i,s_i)` gives a shorter reduced candidate, and
    `N_+(L) <= 3·2^L − 2`.
  * 3(c) is correctly labelled as observed only.
* **Consequences and calibrations.**
  * (C1)–(C3) and (K1)–(K3) checked.
  * The cited items exist as stated in committed established nodes: `(HK1)` `δ^2 ∈ Λ_v`, item 1
    (`Q` residually finite) and item 4 (`(xz)^4 ∉ γ_2(Λ_v)`) of
    `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`, and item 2 (faithfulness) of
    `radu-mark-survives-only-if-horizontal-group-embeds`.
  * All five required claims compute as ESTABLISHED.
* **Recomputation.**
  * Re-ran the artifact script with `LMAX = 17` (single-threaded, about 3 minutes). Its output is
    byte-identical to the committed output file and ends `ALL_OK`.
  * Wrote an independent check (scratch, not landed) with its own table, derived automatically
    from the relator rotations, and a brute-force radius and boundary-vertex search on the ball,
    for all 189 reduced words with `L <= 6`.
    * Every boundary vertex (not just the first) is `o` or ends in `y`.
    * The push through `vz` outputs `vx` with `L(r+1)` moves.
    * The radius facts 3(a) hold.
  * On 300 random involution tuples on 6–40 points (large, unstructured defects), 12000
    instances passed with the raw defects `e_i`:
    * the per-move bound of Step 1 and `(S1)`;
    * `λ_l` for each letter, `(S3)`, and Step 4;
    * `(RL1)`/`(RL3)` and `(EB1)`.
* **Duplicates.** `bin/cairn search --similar` returns the three nodes already handled by
  `distinct_from`. No existing node proves a metric elliptic bound.
* **Literature.** The arXiv export API (fetched 2026-09-16) confirms every listed identifier,
  title, author list and version date. The previously untitled hit arXiv:2605.09493 is
  M. Amir, N. Lazarovich, "Simple Lattices in Products of Davis Complexes" (v1 2026-05-10). Its
  abstract is about constructing simple lattices and does not mention soficity, so it stays
  unused. The 25 most recent arXiv submissions matching "sofic" (latest 2026-08-30) contain
  nothing on soficity of Radu's lattice or the Titz–Witzel kernel. The target's status is
  unchanged.

**Changes.** No mathematical changes. This referee section was added.

**Verdict.** Sound; landed as is. `(EB1)`, `(EB2)`, 3(a), 3(b) and (C1)–(C3) are proved from
established nodes. 3(c) is an observation. Novelty is not claimed, correctly: `(EB2)` is a
quantitative form of item 3 of `radu-mark-survives-only-if-horizontal-group-embeds`, and the
mechanism is Radu's. The result is a necessary condition. It does not make progress on
`radu-commutator-collapse` or on soficity of `K` in either direction.
