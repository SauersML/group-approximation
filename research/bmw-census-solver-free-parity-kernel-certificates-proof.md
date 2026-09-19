---
rg: 2
id: bmw-census-solver-free-parity-kernel-certificates-proof
kind: route
title: Proof by the soundness of the four certificate types over the BMW normal form, and a fresh re-check of every certificate and of census coverage
target: bmw-census-solver-free-parity-kernel-certificates
requires:
  - bmw-census-sat-free-klein-chain-certificates
  - bmw-census-klein-power-chain-certificates
  - bmw-klein-frame-chain-certificates
  - bmw-klein-free-quaternionic-parity-kernels
  - bmw-census-survivor-cone-tree-certificates
  - bmw-census-radius6-cone-lemma-certificates
artifacts:
  - experiments/bmw-census-solver-free-recheck-2026-09-18/README.md
  - experiments/bmw-census-solver-free-recheck-2026-09-18/recheck.py
  - experiments/bmw-census-solver-free-recheck-2026-09-18/recheck.log
  - experiments/bmw-census-solver-free-recheck-2026-09-18/mutate.py
  - experiments/bmw-census-solver-free-recheck-2026-09-18/mutate.log
---

# Proof

The six required claims supply the certificate files. This route does not rely on their checking
scripts. It proves that each certificate type is sound (§2–§5), and `recheck.py` checks every
certificate and the coverage from the census squares alone (§6–§7).

## 1. The group of a class

A class of pattern `mpA_npB` is a list of `mn` squares `[[h,v],[v',h']]`. Each square means the
relation `h v = v' h'`, and letters come with involutions `iA`, `iB` giving inverses.

The rewriting system has rules `c c^{-1} → 1` and `h v → v' h'`. It terminates: the length does not
increase, and the second rule lowers the number of pairs (h-letter before v-letter). Its critical
overlaps are `h h^{-1} v` and `h v v^{-1}`. `check_confluence` resolves both families for every
class used, so by Newman's lemma each element has a unique normal form `V H`: a reduced `v`-word
followed by a reduced `h`-word.

`recheck.py` computes normal forms in two unrelated ways. `nf` pushes letters one at a time, and
`rewrite` applies redexes leftmost-first. `selftest` checks that they agree on 60 random words per
certificate. Equality of elements is equality of normal forms.

The parity kernel `Γ^+` is the set of elements whose normal forms have even `v`-length and even
`h`-length. It has index 4 and is torsion-free (§3 of
`small-degree-bmw-parity-kernels-not-left-orderable-proof`).

Let `P` be the positive cone of a left order on `Γ^+`. Then:
- `P P ⊆ P`;
- `1 ∉ P`;
- for every `g ∈ Γ^+ − {1}`, exactly one of `g`, `g^{-1}` lies in `P`.

Write `|g| = max(g, g^{-1})`. Every certificate below derives a contradiction from `P`.

## 2. Chains (Klein and Klein-power)

**Lemma K.** If `a b a^{-1} = b^{-1}` with `a, b ∈ Γ^+ − {1}`, then `|b| < |a|`.

*Proof.* Replacing `b` by `b^{-1}` preserves the relation. So does replacing `a` by `a^{-1}`, since
`a^{-1} b a = b^{-1}` follows by inverting and conjugating. So we may assume `1 < a` and `1 < b`, and
we suppose `a ≤ b`. The relation gives `b a b = a`. Now `1 < b` gives `a < ab`, so `1 < ab`. Then
`b < b(ab)`. Hence `a = bab > b ≥ a`, a contradiction. ∎

**Lemma R.** Let `x = r^e` and `y = r^f` with `r ∈ Γ`, `x, y ∈ Γ^+ − {1}` and `1 ≤ |e| < |f|`.
Then `|x| < |y|`.

*Proof.* Suppose first that `r ∈ Γ^+`. Then `r ≠ 1` because `x ≠ 1`. Replacing `r` by `r^{-1}` we
may assume `r > 1`. Then `r^k` increases with `k`, so `|r^e| = r^{|e|} < r^{|f|} = |r^f|`.

If `r ∉ Γ^+`, then `r^2 ∈ Γ^+`, since `Γ/Γ^+ ≅ (Z/2)^2`. Moreover `r^k ∈ Γ^+` only for even `k`. So
`e` and `f` are even, and we apply the first case to `r^2`, `e/2` and `f/2`. ∎

**Chain certificate.** This is a cycle `x_0, …, x_{k−1}` in `Γ^+ − {1}`. For each `i`, either
- (K) `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}`, or
- (R) `x_i = r^e` and `x_{i+1} = r^f` with `1 ≤ |e| < |f|`, where the root `r` is given or is `x_i`.

By Lemmas K and R, `|x_0| < |x_1| < ⋯ < |x_0|`, which is impossible. `check_chain` checks the
following:
- every `x_i` is nontrivial and even;
- every step, as (K) by normal forms, or as (R) by searching `|e| ≤ 12` and `|f| ≤ 40`;
- at least one step is (K).

This covers the files `chains_*.json` of `bmw-klein-chains-2026-09-17` (w6c),
`bmw-klein-chains-transposed-2026-09-17` (w7) and `bmw-klein-frames-2026-09-18` (w8).

## 3. Cone-propagation trees

A tree node is either `["split", g, T_1, T_2]` or `["leaf", [x,y], steps]`. A branch carries the set
of split elements chosen along it: `g` into `T_1`, and `g^{-1}` into `T_2`. `check_tree` checks each
of the following:
- every split element is in `Γ^+ − {1}`, so on every branch the assumed set lies in `P` for the
  branch that `P` selects;
- in a leaf, every step `[z,u,w]` has `u, w` already in the set and `z = uw`, so `z ∈ P`;
- at the end `x, y` are in the set and `xy = 1`, so `1 ∈ P`.

Following, at each split, the branch that `P` chooses reaches a leaf whose set lies in `P`. That
leaf gives `1 ∈ P`, a contradiction.

This covers `bmw-klein-free-2026-09-18/tree_*.json` (w9, `31_30` #26 and `31_31` #12) and
`bmw-cone-trees-2026-09-18/trees.jsonl.gz` (w10).

## 4. Cone lemmas

A record has a table `els` of words and lemmas `L_0, L_1, …`. Each lemma has an index set `S_i`,
steps and an end. It asserts `S_i ⊄ P`. Every table entry is checked to be in `Γ^+ − {1}`.

Lemma `L_i` is proved by assuming `S_i ⊆ P` and growing a set `Q ⊆ P`, starting from `Q = S_i`:
- A step `[z,u,w]` needs `u, w ∈ Q` and `z = uw`. Then `z ∈ P`.
- A step `["sq",z,u]` needs `u ∈ Q` and `z z = u`. If `z ∉ P` then `z^{-1} ∈ P`, so
  `u^{-1} = z^{-2} ∈ P`, contradicting `u ∈ P`. So `z ∈ P`.
- A step `["L",j,z]` needs `j < i` and exactly one `s ∈ S_j` outside `Q`, with `z = s^{-1}`. By
  `L_j`, `s ∉ P`. Since `s ≠ 1`, it follows that `z = s^{-1} ∈ P`.

The end is `[x,y]` with `x, y ∈ Q` and `xy = 1`, giving `1 ∈ P`, or `["L",j]` with `j < i` and
`S_j ⊆ Q`, contradicting `L_j`. Either way `S_i ⊄ P`.

The last lemma must have `S = ∅`. Its conclusion `∅ ⊄ P` is false, so `P` does not exist.
`check_lemmas` checks all of this, using indices only below `i`, so there is no circularity. This
covers `bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz` (w11).

## 5. Consequence

For every class with a certificate that passes §2, §3 or §4, `Γ^+` has no positive cone. So `Γ^+` is
not left-orderable, and neither is any group containing it.

## 6. Reducibility test and coverage

`finite_order` computes the images of `⟨A⟩` in `Aut(T_V)` and of `⟨B⟩` in `Aut(T_H)`. It closes a
set of automaton states under right multiplication by generators, with Moore minimisation, and
stops at 4000 elements. A class is *certified reducible* if both images are finite within the cap.
It is a *candidate* otherwise.

The vertical automaton is read off the squares directly. From `h v = v' h'` it follows that
`v'^{-1} h = h' v^{-1}`: in state `v'^{-1}` the input `h` produces output `h'`, with section
`v^{-1}`.

For every class of the 20 patterns, the computed finiteness data agrees with the pipeline's
`out_*.jsonl`, as asserted in `recheck.py`. So the candidate set is exactly the one used by
`bmw-degree-44-53-parity-kernels-not-left-orderable` and
`small-degree-irreducible-bmw-parity-kernels-not-left-orderable`.

## 7. Result

**Result** (`recheck.log`):
- **Certificates:** 1206 certificates on 1203 classes checked, 0 rejected. Three classes have two
  certificates: `40_40` #193, #281 and #332.
- **Census:** 6964 classes. At cap 4000, 5763 are certified reducible. `51_30#506` is also certified
  reducible at cap 60000, with image orders 6 and 6912, as in `bigcap.log`.
- **Candidates:** 1200, and all 1200 have a checked certificate. The other 3 certified classes are
  reducible Promislow-type classes (`41_40` #1174, `41_41` #486 and #541).

| degree | patterns | classes | certified reducible | candidates | covered |
|---|---|---|---|---|---|
| (3,3) | 30_30, 31_30, 31_31 | 60 | 56 | 4 | 4 |
| (4,3) | 40_30, 41_30, 41_31, 42_30, 42_31 | 639 | 589 | 50 | 50 |
| (4,4) | 40_40, 41_40, 41_41, 42_40, 42_41, 42_42 | 3822 | 3133 | 689 | 689 |
| (5,3) | 50_30, 50_31, 51_30, 51_31, 52_30, 52_31 | 2443 | 1986 | 457 | 457 |
| total | 20 | 6964 | 5764 | 1200 | 1200 |

The candidate counts agree with the census claims:
- 62 for (3,3), (4,3) and `42_42` (`small-degree-irreducible-bmw-parity-kernels-not-left-orderable`);
- 301 for `40_40`, which includes #193, #281 and #332;
- 190 for `50_30`.

The certificates come from these families:

| family | classes |
|---|---|
| Klein chains (w6c) | 33 |
| Klein-power chains (w7) | 171 |
| frame chains (w8) | 3 |
| quaternionic cone trees (w9) | 2 |
| cone trees (w10) | 485 |
| cone lemmas (w11) | 509 |

By §5, `Γ^+` is not left-orderable for every candidate. This proves the theorem. The corollary follows
from §1, §5 and §6 of `small-degree-bmw-parity-kernels-not-left-orderable-proof`. By that route, an
irreducible BMW lattice of these degrees is isomorphic to `Γ` for a class in one of the 20 census
files, and it is not certified reducible. ∎

**Mutation test.** `mutate.py` makes 18 corruptions of the four certificate types:
- a chain element replaced, moved outside `Γ^+`, or dropped;
- a reversed power step;
- a chain with no (K) step;
- a dropped or wrong tree step;
- a leaf without a contradiction;
- a split outside `Γ^+`;
- a dropped lemma step;
- a nonempty last lemma;
- a table entry outside `Γ^+`;
- a lemma citing itself;
- a lemma end without a contradiction;
- swapped product factors.

`recheck.py`'s checkers reject all 18 (`mutate.log`: "0 corruptions not rejected").
