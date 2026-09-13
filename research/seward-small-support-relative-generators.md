---
rg: 2
id: seward-small-support-relative-generators
kind: claim
title: Below a fraction r of a base entropy, an ergodic action has a relatively generating pre-partition supported on a set of measure r with prescribed proportions
distinct_from:
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that imports Seward's Part II computations of Bernoulli Rokhlin entropy; this imports the strongest form of the Part I generator theorem, which controls the support of the generator.
  seward-rokhlin-entropy-subadditivity: that imports countable sub-additivity of outer Rokhlin entropy from Part II; this is the Part I generator theorem with support control.
---

**ESTABLISHED (import)** by [[seward-small-support-relative-generators-citation]].

Let `G` be a countably infinite group acting ergodically, not necessarily freely, by measure-preserving
bijections on a non-atomic standard probability space `(X, µ)`, and let `F` be a `G`-invariant
sub-σ-algebra.

- **Pre-partitions.** A pre-partition is a countable family of pairwise disjoint subsets of `X`. The reduced
  σ-algebra `σ-alg^red_G(α)` is the set of Borel `R ⊆ X` for which some conull `X'` has the following
  property: for all `r ∈ R ∩ X'` and `x ∈ X' \ R` there is `g ∈ G` with `g·r, g·x ∈ ∪α` lying in distinct classes
  of `α`.
- **Extension (Lemma 2.2).** If a partition `β` restricts to `α` on `∪α`, then
  `σ-alg_G(β) ⊇ σ-alg^red_G(α)`.
- **Theorem 2.3.** Let `0 < r <= 1` and let `p̄ = (p_i)` be a finite or countable probability vector with
  `h^Rok_G(X, µ | F) < r·H(p̄)`. Then there is a Borel pre-partition `α = {A_i : 0 <= i < |p̄|}` with
  `µ(∪α) = r`, `µ(A_i) = r·p_i` for every `i`, and `σ-alg^red_G(α) ∨ F = B(X)`.

**Use on main.** With `F` trivial and `h^Rok_G(X) = 0`, a generating partition can be read off a set of
arbitrarily small measure. `generators-dense-iff-zero-rokhlin-entropy` turns this into a density criterion.
