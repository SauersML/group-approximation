---
rg: 2
id: titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair
kind: claim
title: The Titz--Witzel kernel is nonsofic exactly when every almost solution of its relators becomes monodromy-free after deleting o(n) points, and every almost solution has consistency deficit at least a fixed multiple of its mark
distinct_from:
  infinite-simple-group-permutation-stable-iff-nonsofic: that equates nonsoficity of a simple group with the collapse of every almost action; this replaces collapse by the weaker, purely combinatorial deletion repair (removing o(n) points kills all monodromy), and the passage back to collapse is property (T), through the partial-action rounding theorem.
  titz-witzel-soficity-is-one-finite-csp: that equates soficity with a marked finite gate; this equates the negation with a repair property of all gate solutions, with an explicit deficit-versus-mark inequality in between.
  titz-witzel-kernel-nonsofic: that is the open nonsoficity assertion; this is an established equivalent form of it, not a proof.
  kazhdan-consistent-partial-models-round-to-finite-actions: that is the general rounding theorem; this is its application to the kernel, together with the converse, which needs simplicity.
---

**ESTABLISHED (unreviewed).** Let `K = <S | R>` be a finite presentation of the smallest Titz
Mite--Witzel kernel of `titz-witzel-kernel-sofic`, with `S` symmetric, and let `kappa` be a
Kazhdan constant for `S` in the convention (KP) of
`kazhdan-consistent-partial-models-round-to-finite-actions`. An *almost solution* is a sequence
`sigma_j : S -> Sym(n_j)` with `d_H(sigma_j(r), 1) -> 0` for every `r in R`. A set `A` is
*consistent* as in `kazhdan-consistent-partial-models-round-to-finite-actions`. The *consistency
deficit* `eta(sigma)` is the least `|[n] \ A|/n` over consistent sets `A`.

1. **Deficit inequality.** For every `sigma : S -> Sym(n)`,

   ```text
   max_(s in S) d_H(sigma(s), 1) <= (2 + 2/kappa^2) eta(sigma).                  (DR1)
   ```

2. **Equivalence.** The following are equivalent.
   * (a) `K` is not sofic.
   * (b) **Deletion repair.** Every almost solution has `eta(sigma_j) -> 0`.
   * (c) Every almost solution has `max_s d_H(sigma_j(s), 1) -> 0`.
   * (d) Every almost solution satisfies `d_H(sigma_j(w), 1) -> 0` for every word `w`.

3. **Soficity form.** `K` is sofic iff some almost solution has `liminf_j eta(sigma_j) > 0`. When
   this holds, the solution may be taken to have `liminf_j max_s d_H(sigma_j(s),1) > 0`. Every
   consistent set of such a solution then misses at least `c_kappa m n_j` points, where
   `c_kappa = kappa^2/(2kappa^2+2)` and `m` is the mark. The open trivial words live at filling
   radius of order `log(1/eps_j)` (`kazhdan-sofic-models-carry-long-scale-monodromy`).

**Why this decomposition.** The nonsoficity direction `titz-witzel-kernel-nonsofic` splits into
two prerequisites, each of which can fail separately.

* **(P1) Rounding.** Consistent sets of density `1 - eta` force collapse at rate `O(eta)`. This is
  item 1, ESTABLISHED, and it is where property (T) and the absence of finite quotients are used
  up.
* **(P2) Deletion repair.** Every almost solution of `K` becomes consistent after deleting `o(n)`
  points. This is item 2(b), OPEN, and equivalent to the target. It concerns only monodromy of
  trivial words inside the Schreier graph of a permutation tuple. It makes no reference to
  unitary representations, and it is a statement about all trivial words, not one fixed relation.

A refutation of (P2) is a sofic approximation of `K`. A proof of (P2) must use that `K` is
specific: it fails for every amenable infinite simple group, by the Folner calibration of
`kazhdan-consistent-partial-models-round-to-finite-actions`. What it must repair is monodromy at
filling radius `>~ log(1/eps)`. In particular, deleting a bounded neighbourhood of the relator
defects does not repair a marked solution (item 3).

Proof in `titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair-proof`.
