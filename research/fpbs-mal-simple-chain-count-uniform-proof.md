---
rg: 2
id: fpbs-mal-simple-chain-count-uniform-proof
kind: route
title: A chain's closed walk in the Cayley tree must fold at a hull path of length at most 4, and deleting the leftmost such hull codes every chain in 184^n ways
target: fpbs-mal-simple-chain-count-uniform
requires: []
artifacts:
  - research/artifacts/fpbs-chain-count-leftmost-merge-2026-09-19.md
  - experiments/fpbs-chain-count-leftmost-merge-2026-09-17/offdiag.py
  - experiments/fpbs-chain-count-leftmost-merge-2026-09-17/folding_check.py
  - experiments/fpbs-chain-count-leftmost-merge-2026-09-17/folding_check_out.txt
---

Direct proof. Details are in the artifact, §§0–4.

**0. Tree facts.** The class `Ky` goes to the hull `X(Ky) = y^{-1} T_K` in
the Cayley tree `T`. The following hold:
- (S) this is a bijection, and hull stabilizers act freely on vertices;
- (T0) distinct hulls share no vertex of the same core type;
- (F1) distinct hulls share at most 2 edges, because the off-diagonal part
  of the core's fibre product is two trees with 2 edges each
  (`offdiag.py`);
- (P) ordered pairs of distinct hulls have trivial stabilizer, by
  malnormality;
- (O) relative positions are exactly the diagonal orbits of such pairs.

These are steps 1–3 of `fpbs-mal-two-step-relative-position-rigidity-proof`,
re-derived in artifact §0.

**1. Connectors.** Choose, equivariantly, an exit vertex `out(X, Y) in X`
and an entry vertex `in(X, Y) in Y` for each ordered pair of distinct
hulls:
- the bridge endpoints if the hulls are disjoint;
- a common vertex if they meet.

Given `X` and `D`, the exit vertex determines `Y` (Lemma 1.1). In a chain
`X_0..X_n`, the *hull path* `p_i ⊂ X_i` runs from the entry vertex of `X_i`
to its exit vertex.

**2. Folding (Lemma 2.1).** Suppose `X_0 ∩ X_n ≠ ∅` and `n >= 2`. Then some
interior `p_i` has length at most 4.
- The chain gives a closed walk `p_0 β_1 p_1 ... β_n p_n`, where the
  `β_i` are bridges.
- A bridge never cancels against an adjacent hull path, because it leaves
  that hull at once.
- Two adjacent hull paths cancel in at most 2 edges, by (F1).
- If every interior hull path had length at least 5, the word would
  therefore stay nonempty after free reduction. A closed walk in a tree
  reduces to the empty word, a contradiction.

**3. Merge (Lemma 3.1).** Let `w` be the word of `p_i`. Then the triple
`(X_{i-1}, X_i, X_{i+1})` is determined up to the diagonal action by
`(D_i, w, D_{i+1})`. Hence `D(X_{i-1}, X_{i+1}) = M(D_i, w, D_{i+1})`,
and, by (P), `X_i` is recovered from its two neighbours. There are at most
46 words `w` of length at most 4.

**4. Count (Theorem 4.1).**
1. Repeatedly delete the leftmost interior hull whose hull path has length
   at most 4.
2. Hulls two or more places to the left keep their neighbours, so the
   leftmost index drops by at most one per step.
3. So the index sequences number at most `binom(2n-4, n-2) <= 4^{n-2}`.
4. The code (indices and words) determines the chain.
5. Hence `N_n <= 4^{n-2} 46^{n-1} <= 184^n` for all endpoints with
   intersecting hulls, including `K`, `Kb` (both hulls contain `1`). ∎
