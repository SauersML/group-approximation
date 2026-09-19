---
rg: 2
id: atlas-steinberg-spare-index-independence-proof
kind: route
title: Joint induction with the corrected transfer identity, acyclic by length bookkeeping
target: atlas-steinberg-spare-index-independence
requires: [atlas-steinberg-transfer-identity, atlas-steinberg-context-absorption]
---

# Joint induction with the corrected transfer identity, acyclic by length bookkeeping

The complete proof is `research/artifacts/steinberg-spare-index-2026-08-15.md`
(with §11 reconciling it against the predecessor derivation artifact);
it was adversarially verified with every critical identity re-derived by
hand.  The skeleton:

**Four statements per length, proved in order `(P_t) < (R_t) < (Q_t) <
(Q′_t)`.**  `(P_t)`: all legal chains agree.  `(R_t)`: the splitting law
at every split point and every spare.  `(Q_t)`: derived objects commute
with generators in (St2) pattern.  `(Q′_t)`: derived objects commute
with derived objects in (St2) pattern — proved after `(P_t)`, which
frees the representative, dissolving the old sigma-proviso.

**The acyclicity, which was the entire difficulty.**  `(P_t)` applies
the corrected transfer identity with `x = X_ik(a₁)`, `y = X_km(a₂)`,
`z = Ê_mj(v′)`; its five hypothesis instances sit at lengths
`(1, t−2)`, `2` (the emitted anchor `(P₂)`), `t−1`, `(2, t−1)`,
`(t−2, t−1)` — maximum `t−1`, so `(P_t)` draws on nothing at length
`t`.  Verification re-derived this edge list independently from the
proof text (not by re-running the author's checker) and confirmed the
bookkeeping `1 + |u₂| ≤ t−1` exactly because `|v| ≥ 1`.  The three-index
shuffle then forces all three chains equal: `Ê^{(k)} = V_m` for every
spare `m ≠ k`, and with three spares the resulting equalities pin all
values.  `(Q′_t)` inducts on the second word's length with base `(Q_t)`,
choosing `k₁ ∉ {i,j,p,q}` — one of four places the proof consumes the
fifth index.

**Lemma X** is two `(Q′)` instances (same-source and same-target
patterns), and split independence reduces to spare independence at each
length.  Ring consistency is `atlas-steinberg-context-absorption` plus
bilinearity.  The additive extension is the involutivity finding of the
claim body: the symmetric-difference bookkeeping
`Ê(A)Ê(B) = Ê(A △ B)·∏_{A∩B} Ê(w)²` needs the squares, supplied as
emitted relators and propagated to all lengths through `(Q′)`-centrality
— an argument that sits strictly downstream of this induction and must
not be lifted upstream of it.  Assembly: `Ê` satisfies (St1) (the
homomorphism property of the additive extension), (St2) (= `(Q′)`
extended factorwise), (St3) (= `(R)` extended bilinearly), and inverts
the evident `G₀ → St₅(L)` on generators, giving `G₀ ≅ St₅(L)`.

**Verification record.**  Six fixes from the adversarial pass are
incorporated in the artifact's addendum: the ℤ-lift check of the five
emitted Cuntz–Krieger relators (without which the involutivity
counterexample was incompletely justified — they are emitted with
explicit inverses, `atlas_relator_rank5_relations.py:86-103`, hence
sign-correct over ℤ); the C2 attribution to the emitted CK relators
rather than the canonical-word block; "incomparable hypotheses, all
strictly shorter" in place of "weaker hypotheses"; the third-spare count
corrected from three to four (§6.2's `(Q′₂)` base included); two stale
line-number citations; and the note that the 3,000 → 2,980 emission gap
consists only of freely-trivial words and exact duplicates, both
lossless.  Machine cross-checks: the statement itself in `St₅(R)` over
the degree-6-truncated free `F₂`-algebra (9 legal chains per root at
`t = 3`, 27 at `t = 4`, all agreeing; splitting verified at every split
point), plus the identity checks recorded on the transfer-identity node.
