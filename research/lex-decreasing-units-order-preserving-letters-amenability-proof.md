---
rg: 2
id: lex-decreasing-units-order-preserving-letters-amenability-proof
kind: route
title: Compactness kills infinite decreasing monomial chains, order-preserving letters normalize, and the amenable extension feeds the sofic defect model
target: lex-decreasing-units-with-order-preserving-letters-are-amenable
requires:
  - sofic-subgroups-carry-independent-cylinder-defects
artifacts:
  - research/artifacts/multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md
---
Artifact Section 3 (Lemmas 3.1, 3.2 and 3.4, Corollary 3.3, Theorem 3.5, Example 3.6). Held OPEN until `w4-vf-gate`
re-derives it.
1. **Subalgebra** (Lemma 3.1). A nonzero product has `v' = wu` or `w = v'u`. In both cases the composite range lies
   left of the composite domain.
2. **Local nilpotence** (Lemma 3.2).
   * If infinitely many words are nonzero, König's lemma gives an infinite branch. Its ranges are decreasing nonempty
     cylinders, so they meet in a point `eta`.
   * Pulling `eta` back along the branch gives a strictly increasing sequence, which converges.
   * For large `j` both words of `m_j` are prefixes of the limit, so they are comparable, a contradiction.
3. **Group** (Corollary 3.3). Finitely many elements lie in `1 + N` for a finite nilpotent algebra `N`.
4. **Normalizer** (Lemma 3.4). The terms of `g S[v]T[w] g^-1` have range in `g[v]` and domain in `g[w]`, and
   `g[v] < g[w]` for `g in F`.
5. **Amenable** (Theorem 3.5).
   * `U_< cap F = 1`, since `U_<` is torsion and `F` is torsion-free.
   * Locally finite by amenable is amenable.
   * `iota_A(D_8) <= U_<`, and a nontrivial `P` has elements of infinite order.
   * Apply `sofic-subgroups-carry-independent-cylinder-defects`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 35.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
