---
rg: 2
id: small-window-quasigroup-sub-sfts-have-periodic-points-proof
kind: route
title: Row-window normal form, periodic-cycle hypergraph and level automata turn the small-window cases into a complete branch and bound
target: small-window-quasigroup-sub-sfts-have-periodic-points
requires: [permutive-triangle-sfts-are-quantum-rigid]
artifacts:
  - experiments/triangle-permutive-sft-search-2026-09-17/README.md
  - experiments/triangle-permutive-sft-search-2026-09-17/search.py
  - experiments/triangle-permutive-sft-search-2026-09-17/validate.py
  - experiments/triangle-permutive-sft-search-2026-09-17/run3.log
---

Fix a finite quasigroup `(Q, ⋆)` with `|Q| = k` and the row map `F(r)_i = r_i ⋆ r_(i+1)` on `Q^Z`. A point of
`X_⋆` is a bi-infinite `F`-orbit `(r_t)_(t ∈ Z)` of rows, with `x(i, t) = (r_t)_i`.

## 1. Normal form

Let `Δ_L = {(i, t) : t >= 0, i >= 0, i + t <= L - 1}`. By induction on `t`, the entries `x(i, t)` with
`(i, t) ∈ Δ_L` are functions of the row segment `x(0..L-1, 0)`. So forbidding a set of patterns on `Δ_L` is the
same as forbidding the corresponding set of length-`L` words in every row. Every sub-SFT `Ω ⊆ X_⋆` whose forbidden
patterns have supports inside translates of `Δ_L` is therefore

`Ω(A) = {x ∈ X_⋆ : every length-L word of every row of x lies in A}` for some `A ⊆ Q^L`.

A `w × h` box lies in a translate of `Δ_(w+h-1)`, so boxes with `w + h - 1 <= L` are covered.

**Essential sets.** Put `A^e = L_L(Ω(A))`, the set of `L`-words that occur in rows of points of `Ω(A)`. Then
`Ω(A^e) = Ω(A)` and `A^e ⊆ A`. So it suffices to decide, for every **essential** `A` (one with `A = L_L(Ω(A))`),
whether `Ω(A)` is empty or has a periodic point. The empty set is essential, with `Ω` empty.

## 2. Periodic points (fact P)

**Claim.** `Ω(A)` has a point with a nonzero period iff there are `p >= 1` and an `F`-cycle `C` of `p`-periodic
rows whose cyclic `L`-windows `W_C` all lie in `A`.

- If `C` is such a cycle, stacking the rows of `C` gives a doubly periodic point of `Ω(A)`.
- Conversely, suppose `x ∈ Ω(A)` has a period `v ≠ 0`. The `v`-periodic points of a `Z^2`-SFT form a nonempty
  `Z`-SFT on a transversal strip, and a nonempty `Z`-SFT has a periodic point. So `Ω(A)` has a doubly periodic
  point `y`. Its rows are `p`-periodic for some `p`, and `F` permutes the finitely many `p`-periodic rows
  occurring in `y`. The bi-infinite orbit of `y` therefore lies on one `F`-cycle `C`, and `W_C ⊆ A`.
- This is also Proposition 5 of `permutive-triangle-sfts-are-quantum-rigid` for the row-periodic case.

**Hypergraph.** Call the sets `W_C` *edges*. An essential `A` gives an aperiodic `Ω(A)` iff `Ω(A)` is nonempty
and `A` contains no edge. Because containment is monotone, only inclusion-minimal edges matter.
`cycle_edges(T, k, L, P)` lists all edges with `p <= P` by exhaustive enumeration of `Q^(Z/p)`.

## 3. Emptiness (fact E)

Let `Z_n(A) = {r ∈ Q^Z : F^t r` has all `L`-words in `A` for `0 <= t <= n}`, a `Z`-subshift.

**Claim.** `Ω(A) = ∅` iff `Z_n(A) = ∅` for some `n`.

- If `x ∈ Ω(A)`, then every row of `x` lies in every `Z_n(A)`.
- If every `Z_n(A)` is nonempty, then by compactness some row `r` has all `F^t r` legal for `t >= 0`. That gives
  a legal upper half-plane configuration. Translate it down by `m` and take a limit point as `m → ∞`: the limit
  lies in `Ω(A)`.

**Presentation.** `level_run` builds labelled graphs `G_n` presenting `Z_n(A)`.

- `G_0` is the one-state full shift.
- A state of the product graph is a pair `(u, s)`: `u ∈ Q^(L-1)` is the last `L-1` letters read, and `s` is a
  state of `G_n`.
- Reading a letter `a` with `w = u a ∈ A` moves the `G_n`-component along the letter `u_last ⋆ a`, which is the
  next letter of `F r`. Words `w ∉ A` have no transition.
- A bi-infinite path reads `r` iff every word of `r` lies in `A` and `F r` is read by `G_n`. So the product
  presents `Z_(n+1)(A)`.
- `trim_minimize` deletes states with no incoming or no outgoing edge, iterated. The remaining states are exactly
  the states on bi-infinite paths, so the presented shift is unchanged.
- It then merges states with equal follower-set classes by Moore refinement of the deterministic partial
  automaton. Merging states with equal right-infinite languages does not change the set of labels of
  bi-infinite paths.
- `Z_n(A)` is empty iff the trimmed graph is empty.

**Monotonicity.** If `A ⊆ A'`, then `Z_n(A) ⊆ Z_n(A')` and `Ω(A) ⊆ Ω(A')`.

## 4. Sound certificates

**Certification.** A closed walk in the trimmed `G_n` reads a periodic row `r`. `legal_cycle` iterates `F` on `r`
exactly, over finitely many `p`-periodic rows, until a row repeats. It checks every window of every visited row
against `A`. If all are legal, the eventual cycle `C` satisfies `W_C ⊆ A`. This is a genuine edge, so it may be
added to the hypergraph. Adding edges only ever makes a pruning rule "A contains an edge" apply more often, and
every edge is genuine, so soundness is kept.

**Language bound.** Let `lang = L_L(Z_(n_q)(A_max))` with `n_q = 8`, read off the trimmed graph. Suppose `A` is
essential and `A ⊆ A_max`. Then

`A = L_L(Ω(A)) ⊆ L_L(Z_(n_q)(A)) ⊆ L_L(Z_(n_q)(A_max)) = lang`.

## 5. Completeness of the branch and bound

A search node is a pair `(IN, OUT)` of disjoint word sets. It stands for the essential sets `A` with
`IN ⊆ A ⊆ A_max = Q^L \ OUT`. At the root `IN = OUT = ∅`, which covers all essential `A`.

**Invariant.** Every essential `A` giving a nonempty aperiodic `Ω(A)` lies in the family of some node that is still
being processed or is recorded as a candidate. The steps below preserve it.

1. **Empty prune.** If `Z_8(A_max) = ∅`, every `A` in the family has `Ω(A) ⊆ Ω(A_max) = ∅`.
2. **Language prune.** If `IN ⊄ lang`, no essential `A` in the family exists, by §4. Otherwise replace `OUT` by
   `OUT ∪ (A_max \ lang)`; this loses no essential `A`.
3. **Forced periodic.** If some edge `e` has `e ∩ OUT = ∅` and `e ⊆ IN`, every `A` in the family contains `e`, so
   `Ω(A)` has a periodic point (§2).
4. **Branch.** Otherwise pick an edge `e` with `e ∩ OUT = ∅`, and let `w_1, …, w_m` be the words of `e \ IN`. An
   aperiodic `A` does not contain `e`, so it misses some `w_j`. Let `j` be the least such index. Then `A` lies in
   the child `(IN ∪ {w_1, …, w_(j-1)}, OUT ∪ {w_j})`. The children cover the family, and they are pairwise
   disjoint.
5. **Leaf.** If no edge avoids `OUT`, run `G_n` up to `n = 60`.
   - If it is empty, the family is empty-or-periodic by step 1.
   - If it is alive and some closed walk certifies a new edge (§4), add the edge and re-process the node.
     Termination holds because there are finitely many subsets of `Q^L`, and each re-processing adds a new
     non-superset edge that avoids `OUT`.
   - Otherwise record `A_max` as a candidate.

**Conclusion.** When the search ends with zero candidates, every essential `A`, and hence every `A`, gives an
empty `Ω(A)` or an `Ω(A)` with a periodic point.

## 6. Isomorphism reduction

Relabelling `Q` by a permutation `π` maps `X_⋆` onto `X_(⋆^π)` and carries sub-SFTs with window `L` to sub-SFTs
with window `L`. So one quasigroup per isomorphism class suffices. `iso_reps` returns 1, 5 and 35 classes for
`k = 2, 3, 4`, matching the known numbers of quasigroups of orders 2, 3 and 4 up to isomorphism.

## 7. Runs and checks

- The runs in the artifact logs report `candidates=0` for every square in the stated scope, with `leaves=0`: every
  leaf was resolved by an emptiness certificate or by certification.
- `validate.py` cross-checks facts (P) and (E) on random `A` against brute force:
  - a periodic `A` never tests empty;
  - an alive level-12 graph has legal cone words;
  - an empty verdict at level `n` has no surviving periodic row of small period.
- The result was 0 disagreements in 193 empty cases.
- The first uncertified run reported 77 spurious leaves at `k = 2`, `L = 5`. Each had a periodic row of period
  larger than `P`, and certification resolved all of them. That is why step 5 certifies before recording a
  candidate.
