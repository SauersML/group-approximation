---
rg: 2
id: cyclic-centralizer-host-pentagon-census-proof
kind: route
title: Enumerate the 5-cycle tuples, normalize each relator by explicit automorphisms, and kill torus and Baumslag--Solitar forms with cyclic centralizers
target: cyclic-centralizer-host-pentagons-have-two-relation-orbits
requires:
  - zero-divisor-support-subgroup-host-constraints
---

(1) **Tuples.** A 5-cycle carries `[a_1, b_1, ..., a_5, b_5]` with entries in
`supp alpha` and consecutive entries distinct, cyclically. This is the
inequality pattern of A--T Remark `r-K3-K3`, which rests on their
Thm K3-K3. The relator is `prod_i a_i^-1 b_i`. `cycle_relators.py`
enumerates `2^10 + 2 = 1026` tuples and 105 classes (`census2345.out`).

(2) **Normal forms.** For each relator `r` a breadth-first search over
elementary Nielsen moves, conjugation moves and signed letter permutations
reaches `phi(r)` for an automorphism `phi`. As in
`kaplansky-graph-squares-central-trefoil-proof`, generators
`p = phi^-1(h_2)` and `q = phi^-1(h_3)` of `H` then satisfy `phi(r)(p, q) = 1`.
The census reports the least length reached and the matching pattern.

(3) **Contradictions in every host.**
- A primitive relator, or a proper power of one, makes `H` cyclic. A proper
  power `w^j` is first replaced by `w`, since `H` is torsion-free.
- `p q^m p^-1 q^-n` with `|m| = 1` or `|n| = 1`, or `p^2 q^(+-2)`, makes `H` a
  quotient of `BS(1, j)` or of the Klein bottle group, so solvable. That
  contradicts item 3 of `zero-divisor-support-subgroup-host-constraints`.

(4) **Contradictions with cyclic centralizers.**
- If `p^a = q^b` with `a, b != 0`, the centralizer of `p^a != 1` contains `p`
  and `q`, so `H` is cyclic.
- If `p q^m p^-1 = q^n` with `m, n != 0`, put `M = C_G(q^m)`, a cyclic group
  containing `q`. Every cyclic subgroup containing `q` centralizes `q^m` and
  `q^n`, so `M = C_G(q) = C_G(q^n)`. Conjugation by `p` sends `M` to
  `C_G(q^n) = M`, so `p` normalizes the infinite cyclic group `M`, and `p^2`
  centralizes it. Then `C_G(p^2)` is cyclic and contains `p` and `q`, so `H` is
  cyclic.

(5) **Remaining classes.** 36 classes match no pattern. Their least forms,
up to rotation, inversion and signed letter permutation, are the two words
of item 3 of the claim.
