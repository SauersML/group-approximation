---
rg: 2
id: radu-simple-six-six-lattices-are-not-left-orderable-proof
kind: route
title: A verified positive-cone contradiction in the commutator subgroup of Gamma_{4,4}, pushed up through abelian quotients
target: radu-simple-six-six-lattices-are-not-left-orderable
requires: []
artifacts:
  - experiments/lo-certificate-radu-lattices-2026-09-17/verify_certificate.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/derived_check.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/certificate-gamma44-derived-L6.txt
  - experiments/lo-certificate-radu-lattices-2026-09-17/ab_search.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/bmw.py
  - experiments/lo-certificate-radu-lattices-2026-09-17/run.log
---

**Lemma 1 (certificate soundness).** Let `H` be a group and `E ⊂ H \ {1}` a finite set closed
under inversion with no element of order 2. Let `T ⊂ E^3` be a set of triples with `pq = r` in
`H`. Suppose no `P : E → {0,1}` satisfies both `P(g^{-1}) = 1 − P(g)` and `P(p) ∧ P(q) ⇒ P(r)`
for all triples in `T`. Then `H` is not left-orderable.

*Proof.* The positive cone of a left order is a semigroup and contains exactly one of `h` and
`h^{-1}` for every `h ≠ 1`. Its indicator would satisfy all the constraints. □

**Step 1: the relators are Radu's.** `RADU_44` and `RADU_66` in `bmw.py` were compared
mechanically against the arXiv TeX source of 1712.01091 on 2026-09-17, using a regex over
line 2273 (the four squares of `Γ_{4,4}`) and the row `Γ_{6,6,2}` of Table 6. The sets agree.
The class `BMW` asserts that the link is complete bipartite, with exactly one square for each
pair consisting of a b-letter `v^{±1}` and an a-letter `u^{±1}`.

**Step 2: each triple is a product relation.** `verify_certificate.py radu44 FILE kernel` rewrites
`p q r^{-1}` to the empty word using only free reductions and the moves `v u → u' v'`, where
`v u v'^{-1} u'^{-1}` is a cyclic rotation of a relator or of its inverse. Each move is an equality
in `Γ_{4,4}`. The same verifier, unchanged, validated the Rattaggi certificates.

**Step 3: the elements are nontrivial, in `Γ_{4,4}'`, and not involutions.**
- *Nontrivial.* A rewritten word ends as `A B`, with `A` a reduced a-word and `B` a reduced b-word.
  `Γ_{4,4}` acts simply transitively on the vertices of `T_4 × T_4`, and `A B` moves the base
  vertex to distance `(|A|, |B|)`. So nonempty normal words are nontrivial, and the verifier
  asserts they are nonempty.
- *In the commutator subgroup.* `derived_check.py` computes the exponent-sum vector of each
  word in `Z^{a_1,a_2,b_1,b_2}`. It tests whether that vector is an integer combination of the
  four relator vectors `(1,−1,2,0)`, `(1,1,0,0)`, `(1,−1,−1,−1)` and `(1,−1,−1,1)`, by exact
  rational elimination and an integrality test. That span is exactly the kernel of
  `Z^4 → Γ_{4,4}^{ab}`. A word lies in `[Γ,Γ]` iff its image in `Γ^{ab}` vanishes.
  - Output: 372 words checked, 0 outside `[G,G]`.
  - Negative controls: `a_1 b_2` is outside the span. On the `Γ_{4,4}^+` certificate, 159 of 210
    words are outside, as expected, since that certificate lives in the larger group `Γ_{4,4}^+`.
- *Not involutions.* `Γ_{4,4}` is torsion-free (Radu).

**Step 4: unsatisfiability.** The verifier's complete DPLL prints
`triples verified: 124 variables: 69 / DPLL nodes: 71 / CNF satisfiable: False / CERTIFICATE VALID`.
Independently, CaDiCaL 1.5.3 found the certificate on the radius-6 ball of `Γ_{4,4}'` with short
factors of length at most 4 (`ab_search.py 6 4 derived`), and deletion minimization reduced it.
With short factors of length at most 2 the CNF is SAT (`run.log`). By Lemma 1, `Γ_{4,4}'` is not
left-orderable. □ (part 1)

**Lemma 2 (the seed embeds).** Let `Γ` be a `(d_1,d_2)`-group whose squares include the four
squares of `Γ_{4,4}` on non-involution letters `a_1, a_2, b_1, b_2`. Then `⟨a_1,a_2,b_1,b_2⟩ ≤ Γ`
is isomorphic to `Γ_{4,4}`, via the identity on letters.

*Proof.* Elements of `Γ` correspond bijectively to normal forms `A B` (vertices of `T_1 × T_2`).
The product of two normal forms is computed by moving b-letters past a-letters with the swap map
`v u ↦ u' v'` read from the squares. For the 16 pairs `v ∈ {b_1^{±1}, b_2^{±1}}`,
`u ∈ {a_1^{±1}, a_2^{±1}}`, the square containing `(v,u)` is one of the four `Γ_{4,4}` squares, because
the links of both complexes are complete. So the swap stays inside these letters and agrees with
the swap of `Γ_{4,4}`. Hence normal forms over `a_1, a_2, b_1, b_2` are closed under the product
of `Γ`, and that product coincides with the product of `Γ_{4,4}`. □

**Part 2 (transfer).** Let `N ⊴ Γ` with `Γ/N` abelian, and `N ≤ S`. The composite
`Γ_{4,4} → Γ → Γ/N` has abelian image, so it kills `Γ_{4,4}'`. Therefore
`Γ_{4,4}' ≤ N ≤ S`. A subgroup of a left-orderable group is left-orderable, so `S` is not
left-orderable. □

**Part 3 (the 160 simple groups).**
- Radu, §6.1, states that every `Γ_{6,6,k}` contains `Γ_{4,4}` in the sense of Lemma 2: its
  table lists the squares added to the four of `Γ_{4,4}`.
- Radu computes, with GAP, the order of `Q = Γ_{6,6,k}/⟨⟨[a_1^3,a_2^4]⟩⟩`, and the kernel is
  `Γ^{(∞)}`. He finds `|Q| = 4`, with `Γ^{(∞)} = Γ^+` and `Q ≅ (C_2)^2`, for
  `k ∉ {104,116}`. For `k ∈ {104,116}` he finds `Q ≅ (C_2)^2 × C_3`.
- In every case `Q` is abelian, so Part 2 gives that `Γ_{6,6,k}^{(∞)}` is not left-orderable.
- Simplicity and pairwise non-isomorphism are Radu's theorem.
- Type F: `Γ^{(∞)} ≤ Γ^+` acts freely (Radu, §3 lemma) and cocompactly on the CAT(0) square
  complex `T_6 × T_6`. □

**Additional certificates, same pipeline.**
- `certificate-gamma44-kernel-L6.txt`: `Γ_{4,4}^+`, 70 triples, VALID.
- `certificate-gamma662-kernel-L4.txt`: `Γ_{6,6,2}^+`, 169 triples, VALID. `Γ_{6,6,2}` has torsion,
  but `Γ^+` is torsion-free by Radu's §3 lemma, so the no-involution hypothesis holds.

*Review status.* Machine-checked twice, by independent code paths: normal-form multiplication
with CaDiCaL, and relator rewriting with DPLL plus exact-arithmetic membership. No human has
checked the certificate line by line. The trust points are:
- Radu's TeX source;
- Radu's GAP computation of `Γ_{6,6,k}/Γ^{(∞)}`, which is imported, not recomputed here;
- his simplicity theorem.
