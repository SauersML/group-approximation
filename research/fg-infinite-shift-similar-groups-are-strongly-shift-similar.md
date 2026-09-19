---
rg: 2
id: fg-infinite-shift-similar-groups-are-strongly-shift-similar
kind: claim
title: Every finitely generated infinite shift-similar group is strongly shift-similar (the finitely generated form of Mallery-Zaremsky Question 3.18); if true, Mallery-Zaremsky Question 5.13 is fully answered
distinct_from:
  infinite-shift-similar-groups-need-not-be-strongly-shift-similar: that answers Question 3.18 as printed, with a group that is not finitely generated; this is the finitely generated version, which is what Observation 5.12 and Question 5.13 of the source need.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `infinite-shift-similar-groups-need-not-be-strongly-shift-similar`, `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`.

**OPEN.** A yes or no answer both count as progress.

**Statement.** If `G <= Sym(N)` is infinite, shift-similar and finitely generated, then `psi_infinity` is onto,
i.e. `G` is strongly shift-similar (Mallery--Zaremsky arXiv:2202.00822v2, Definition 3.17).

**Equivalent germ form.** Let `c` be conjugation by the shift `σ(i) = i+1` on `Sym(N)/FSym(N)`, as in step 1 of
`infinite-shift-similar-groups-need-not-be-strongly-shift-similar`. The statement says: no finitely generated
subgroup `Γ <= Sym(N)/FSym(N)` satisfies `c(Γ) ⊊ Γ`.
- *Why this is equivalent.* An infinite shift-similar `G` contains `FSym(N)` (Theorem 3.12), so it is the preimage
  of `Γ = G/FSym`. It is finitely generated iff `Γ` is, because `FSym(N)` is the normal closure of one
  transposition. Shift-similarity is `c(Γ) ⊆ Γ`, and strong shift-similarity is `c(Γ) = Γ`.
- *Near-action form.* A counterexample `Γ` makes `Δ = < Γ, σ̄ >` a finitely generated subgroup of the near
  symmetric group whose index-zero part `∪_k c^-k(Γ)` is a strictly ascending union. It is therefore not finitely
  generated (compare Corollary 5.6 of the source).
- *A test case, now refuted.* `c(x) = x^2` with `x` of infinite order would give one, since `c(<x>) = <x^2>`. That is a near
  action of `BS(1,2)` in which `t` acts as the shift. None exists, and more generally no cyclic `Γ` works
  (`no-nontrivial-germ-is-shift-conjugate-to-a-proper-power`). A counterexample needs at least two generators.

**Why it matters.**
- If true, every group satisfying the hypotheses of Question 5.13 (finitely presented, or of type `F_m`) is finite
  or strongly shift-similar.
  - Finite shift-similar groups are the `S_m` (Lemma 3.6), with `H_n(G) = H_n` (Observation 5.2), of type
    `F_(n-1)` (Brown).
  - The strongly shift-similar case is `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`.
  - So all three sentences of Question 5.13 would be answered positively.
- If false, a finitely generated counterexample would test sentences 1–2 of Question 5.13 on a genuinely new
  class. Its `H_1(G)` is not finitely generated (Observation 5.12).

**Attempts.**
- *Sparse transpositions* (the non-finitely-generated example). Adding finitely many generators that shift the
  sparse pattern tends to add the flip-type germs of `E_2`, which make `c` onto again. An example: `x` a sparse
  product of transpositions on even pairs, and `μ` the flip `(1 2)(3 4)...`. Then `c(x) = μ x μ`, and
  `c(< x, Germs(E_2) >) = < x, Germs(E_2) >`.
- *Commensurated subsets for `BS(1,2)`* (superseded: `no-nontrivial-germ-is-shift-conjugate-to-a-proper-power` proves no such near action exists). The affine action on `Z[1/2]` (`a = +1`, `t = /2`) was tried with subsets
  `{y >= 0 : den(y) <= f(y)}`. None is commensurated by both `a` and `t`: bounded denominators break `t`, and
  unbounded ones break `a` at infinitely many jumps. No counterexample and no proof.
- *Sparse transpositions plus one window rotation.* Take `x = rho̅_0` of the non-finitely-generated example, and let
  `y` rotate each window `W_i = [2^(i-1)+2, 2^i+1]` down by one step.
  - For each `k`, `y c^k(x) y^-1 = c^(k+1)(x)` at infinity, so `< x, y >` contains every `c^k(x)`.
  - It fails: `c(y) = z y`, where `z` carries `2^i` to `2^(i+1)` across windows. But `< x, y >` preserves every
    `W_i`, so `c(< x, y >)` is not contained in `< x, y >`.
  - Lesson: a finitely generated `Γ` with `c(Γ) ⊆ Γ` cannot preserve a window structure unless that structure is
    shift-invariant up to `Γ`. Making it shift-invariant tends to make `c` onto.
- *Candidate source of examples (untested).* Residue-class-wise affine permutations of `N` (Kohl's RCWA groups)
  are closed under `c` and `c^-1`, and they contain many finitely generated subgroups. A finitely generated RCWA
  subgroup with `c(Γ) ⊊ Γ` would settle the node negatively.
- *Bounded GAP/RCWA search, 2026-09-18* (artifact `research/artifacts/gq-bh-bh-houghton-presentation-rcwa-search.md`).
  - The calibration passed, the planted positives were found, and the power lemma's prediction of zero hits held.
  - Shifted class transpositions (6 seeds, `L <= 3`) showed no forward or backward closure within word balls of up
    to about 9300 elements.
  - No Thompson-`F` prototype (`x_0` acting as the shift) turned up among 1870 small RCWA⁺ elements of index 0.
  - This is weak evidence that the statement is true. It proves nothing.

**Lesson for general BH (from the search).** Inside RCWA⁺(Z) the shift acts on germs of class transpositions by
drifting affine offsets. Short-word closure of these drifting families never appeared, in either direction. A
positive answer to this node (f.g. ⇒ strongly shift-similar) would complete Mallery--Zaremsky Question 5.13. A
proof would most likely come from a `Σ^1` symmetry argument for subgroups of `NearSym(N)` containing the shift,
generalizing the end count of `no-nontrivial-germ-is-shift-conjugate-to-a-proper-power`, rather than from a search.
- *Proof attempts toward the `Σ^1`-symmetric form* (coordinator's route, 2026-09-18). The target is "never exactly
  one-sided", not "always two-sided". The latter is false: see the calibration on
  `shift-similar-germ-groups-are-ascending-hnn-extensions`. Partial facts, with elementary proofs:
  - *Supports are cofinite.* Let `B` be finitely generated with `c(B) ⊆ B`, and let `S` be the union of the
    supports of its generators, modulo finite sets. Then `S - 1 ⊆ S` modulo finite. So if `n ∈ S` is large, then
    `n - 1 ∈ S`, and `S` contains a tail `[n_1, ∞)` unless `B = 1`. This is exactly what kills sparse examples in
    the finitely generated setting.
  - *Orbits are downward refining.* The `c(B)`-orbits are the `B`-orbits shifted down by one, and they refine the
    `B`-orbits. The parent-map argument of `no-nontrivial-germ-is-shift-conjugate-to-a-proper-power` then suggests
    that the orbits are eventually residue classes mod some `d`. This is not written out; bottom effects from
    finitely many orbits meeting the bad region still need care.
  - *Thompson-type realizations fail for a dynamical reason.* Suppose `t^-1 B t ⊊ B` is realized with `B` supported
    on a region `I` that `t` expands. Then points of `I` have infinite backward `t`-orbits, while under the shift
    (one ray) every backward orbit is finite. This kills the natural embeddings of `F = <x_0,x_1>` with
    `t = u x_0` and `u` supported off `supp(B)`.
  - *Bounded displacement.* Pass to the two-sided limit subshift `Ω` of the generators' displacement data. For
    every limit configuration `y`, `c(B) ⊆ B` becomes `Γ_(Ty) ⊆ Γ_y` inside `Sym(Z)`. For recurrent `y` this gives
    only density of `Γ_(Ty)` in `Γ_y` in the pointwise topology, i.e. the same orbits on all finite tuples, not
    equality. Non-recurrent (sparse) features, where properness hid in the infinitely generated example, are
    invisible in `Ω`.
  - No proof of the symmetric statement. The next tractable case is abelian `B`, by orbit-type counting (the cyclic
    case is the lemma).
