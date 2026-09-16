---
rg: 2
id: basilica-group-is-torsion-free-and-contains-every-z-n-proof
kind: route
title: Section-word induction proves the Basilica group torsion-free with free abelian subgroups of every rank
target: basilica-group-is-torsion-free-and-contains-every-z-n
requires: []
artifacts:
  - research/artifacts/basilica-group-torsion-free-2026-09-16.md
---

The full proof is in the artifact. It uses only the recursion `a = (1, b)`, `b = (1, a)ε` and the
composition rule `(p_0, p_1)ε^c · (q_0, q_1)ε^s = (p_0 q_c, p_1 q_(c+1)) ε^(c+s)`.

1. **Section words (Lemma 1).** Each letter of a word `w` puts exactly one letter into one of the
   two section words. So `|w_0| + |w_1| = |w|`, and the exponent sums of `a` and `b` are exchanged
   between `w` and its sections.
2. **One-coordinate words (Lemma 2).** If every letter of a freely reduced `w` contributes to the
   same coordinate, then `w` is `a^k`, `a^k b`, `b^(−1) a^k` or `b^(−1) a^k b`. This follows from
   the parity bookkeeping in Lemma 1.
3. **Infinite order (Lemma 3).** From `a^k = (1, b^k)` and `b^(2m) = (a^m, a^m)`: a minimal `k`
   with `a^k = 1` would give a smaller one.
4. **Exponent sums (Lemma 4).** Induction on the length of a trivial word. If both sections are
   nonempty, they are shorter. Otherwise step 2 reduces to `a^k = 1`. So `B^ab ≅ Z^2`.
5. **Torsion-freeness (Theorem 5).** Induction on geodesic length. A torsion element has
   `ε_b = 0`, so it lies in `St(1)` with torsion sections. Either both sections are strictly
   shorter, or by step 2 the element is conjugate to a power of `a`.
6. **Rank (Proposition 6).** `[a, b^2] = (1, [b, a])`, the projection `St_B(1) → B` onto the second
   coordinate is onto, and `b^(−1)(x, 1)b = (1, x)`. So `B' ⊇ B' × B'` geometrically. Iterating
   gives `(B')^(2^k) ≤ B`. With `[b, a] ≠ 1` of infinite order, this gives `Z^(2^k) ≤ B`, and hence
   `cd B = ∞`.
7. **Substitution (Proposition 7).** `σ(g) = (a^(ε_a(g)), g)` is a homomorphism because `ε_a` is
   one, and it is injective through its second coordinate. The powers of `a^b = (b^a, 1)` lie in
   pairwise distinct cosets of `σ(B)`.
8. **HNN extension (Corollary 8).** Every element of `B~` has the form `t^p g t^(−q)`. A torsion
   element is killed by `χ : B~ → Z`, hence is conjugate into `B`. The valence of the Bass–Serre
   tree is `1 + [B : σ(B)]`.

A machine sanity check of the conventions and identities is in
`experiments/basilica-hnn-2026-09-16/basilica_checks.py`, with output in `basilica_checks.out`
(all PASS). It is evidence for the conventions, not part of the proof.
