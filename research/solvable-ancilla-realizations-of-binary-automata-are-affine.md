---
rg: 2
id: solvable-ancilla-realizations-of-binary-automata-are-affine
kind: claim
title: A binary automaton with identity ancilla tracks that is sitewise conjugate to a polynomial automaton over a finite solvable group is affine, and non-affine content always lives above the solvable radical
distinct_from:
  linearly-dirty-ancilla-words-realize-only-affine-data-maps: that is words of linear track moves and exact reads over the ring Z; this is arbitrary words with constants in any finite solvable group acting on the whole alphabet {0,1} x B, over every host group, and the invariant is a chief-series crossing index instead of a row vector of a matrix over Z[G].
  formalizable-binary-pairs-over-biorderable-groups-are-affine: that is formal one-track left-inverse pairs over F_2 on bi-orderable hosts, with no ancilla; this allows every identity of the alphabet group, any number of identity ancilla symbols and every host, and needs no left inverse.
  nilpotent-polynomial-automata-reduce-to-kaplansky: that reduces surjunctivity of nilpotent-polynomial automata to one-track direct finiteness; this shows that such reductions, and any solvable extension of them, reach no non-affine binary automaton through a stabilized sitewise encoding.
  solvable-polynomial-automata-reduce-to-kaplansky: that makes injective solvable-polynomial automata bijective under direct finiteness of matrix group algebras; this shows that no non-affine binary automaton is sitewise conjugate, with identity ancillas, to a solvable-polynomial automaton, so that reduction reaches no new binary rule.
  injective-binary-automata-are-stably-formalizable: that asks for stabilized formal identities over F_2; this rules out the other natural source of stabilized identities, the laws of a solvable group structure on the stabilized alphabet.
artifacts:
  - experiments/solvable-ancilla-realizations-2026-09-17/check_realizations.py
  - experiments/solvable-ancilla-realizations-2026-09-17/results.txt
---

**ESTABLISHED** by `solvable-ancilla-realizations-of-binary-automata-affine-proof` (proposed; referee
pending).

**Setting.**
- `G` is any group and `tau` an automaton on `{0,1}^G` with any finite memory.
- `B` is a finite set and `Q` a finite group with `|Q| = 2|B|`. `psi : {0,1} x B -> Q` is any bijection, applied
  sitewise.
- `T` is a `Q`-polynomial automaton: `T(z)(g) = w(z(g m_1), ..., z(g m_k))`, where `w in Q * F_k` is a word with
  constants.
- `T` **realizes** `tau` if `T o psi = psi o (tau x id_B)`. Then `T` is conjugate to `tau x id_B` on all of
  `Q^G`, so no injectivity condition on a section is involved.

**Theorem.**
1. **(A) Solvable alphabets.** If `Q` is solvable and `T` realizes `tau`, then `tau` is affine over `F_2`:
   `tau(x) = tau(0) + sum_h x(h) e_h` for fixed configurations `e_h`.
2. **(B) Every alphabet.** If `T` realizes a non-affine `tau`, then every coset of the solvable radical
   `Sol(Q)` lies inside one data fibre `psi({a} x B)`. So `tau x id` is a sitewise factor of the induced
   `Q/Sol(Q)`-polynomial automaton, and all non-affine data sits above the solvable radical.
3. **(C) Sharpness.** For `Q = A_5`, `|B| = 30` and any `psi`, every `tau` with finite memory is realized
   (Maurer–Rhodes functional completeness). So solvability is exactly the threshold.

**Invariant.** Order the congruences of `Q` along a chief series `1 = Q_0 < ... < Q_r = Q`. The **crossing
index** is the least `i` such that some `Q_i`-coset meets both data fibres. The proof shows:
- a non-sitewise `tau` forces the crossing subgroup to contain every ancilla pair;
- an abelian crossing factor then makes each single-site data flip act on the output by a translation that
  does not depend on the configuration.

**Why it matters.** The heretic denial A1 of the target (give the alphabet a group structure and use its
laws) proved `nilpotent-polynomial-automata-reduce-to-kaplansky`. The natural route from there to arbitrary
binary automata is to stabilize `tau` with identity ancilla symbols and encode `tau x id` as a polynomial
automaton over a nilpotent or solvable group of order `2|B|`, then apply that reduction or a solvable extension
of it.
- This theorem kills that route for every non-affine `tau`: over every host, with any number of ancilla
  symbols, any encoding and any word.
- Affine `tau` are already bijective when injective, under direct finiteness of `F_2[G]`. So solvable group
  laws add no surjunctive binary automaton.
- The scope line "No stabilization with ancilla tracks is known" of the nilpotent node becomes a theorem for
  identity ancillas.
- The only group structures that can carry the marker involution `x_i -> x_i + [x_(i-3..i+3) = 001*100]` have
  a nonabelian chief factor above the crossing. There the polynomial clone is complete on the top factor and
  the lower-central-series method has nothing to act on.

**Calibration** (`experiments/solvable-ancilla-realizations-2026-09-17`). The whole two-variable polynomial
clone `Pol_2(Q)` was enumerated completely for `Q = Z2, Z4, Z2xZ2, Z6, S3, Z8, Z4xZ2, Z2^3, D4, Q8`. For
`S3` that is 4251528 functions. For `A4` the first 3284136 functions in breadth-first word order were
enumerated; this part is capped and incomplete. For each clone function, every pairing of the alphabet
and every data labeling were tested, which gives memory `{1, m}`. `results.txt` records:
- no non-affine rule is realized over any of these groups;
- non-sitewise realized rules occur only over `Z2`, `Z6` and `S3`, and are `x(m)`, `x(1) + x(m)` and their
  complements;
- a pipeline control (AND pushed through a `psi`) is detected over every group.

**Escapes not covered.**
- **Several data tracks.** For data alphabets `{0,1}^n` a crossing can separate some tracks before others,
  and the argument gives only a triangular structure.
- **Ancilla dynamics.** The ancilla track evolves by a non-identity automaton.
- **Regrouping.** Encodings along a finite-index subgroup of `G`, as in
  `marker-involution-is-formalizable-after-regrouping`.
- **Non-sitewise encodings.** `psi` replaced by a reversible automaton, that is, realization up to
  topological conjugacy rather than sitewise conjugacy.
