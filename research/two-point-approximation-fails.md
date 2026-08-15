---
rg: 2
id: two-point-approximation-fails
kind: claim
title: The two-point approximation fails at the marked pair — the negation claim
distinct_from:
  two-point-orbit-approximation: that is the assertion this claim negates; per kernel doctrine refutation is the establishment of the negation claim, and exactly one of the two can ever be established.
  exact-models-cannot-separate-marked-pair: that closes the exact-model subclass only; this asserts failure over ALL admissible models at some window and precision, which is strictly stronger and remains open.
  kun-block-transfer-lemma: that is the working lemma; this is its headline consequence, kept separate so the lemma can fail while a different mechanism still establishes this claim.
---

**Claim.**  There exist a finite window `F ⊆ G` and `ε > 0` such that NO
finite set `A`, unital `(F,ε)`-multiplicative `φ : G → Sym(A)`, subset
`S ⊆ A` with `|S| > (1−ε)|A|`, and labels `(j_s)` satisfy the two-point
clauses of `two-point-orbit-approximation` at the marked pair `(Γ, hΓ)`.

**Payoff.**  By the established route
`witness-yields-two-point-approximation` (witness ⟹ two-point), this claim
refutes `hilbert-embeddable-witness-for-kun-thom-wreath` and closes the
Hilbert-embeddable lane of the separation program negatively: the
Kun--Thom wreath would have no Hilbert embeddable weak-soficity witness,
the first obstruction separating weak soficity from the class `𝒞_FU` on an
explicit group.  It does NOT establish the goal's separation by itself —
it prunes the witness lane either way and redirects effort to the
surviving routes.

**Known constraints on any proof.**  Exact models fail already
(`exact-models-cannot-separate-marked-pair`), parity models fail at the
trap window (`parity-trap-window`), and any proof must choose `F ⊇ F*`
since below the trap the claim is false
(`parity-flip-models-satisfy-two-point`).  The surviving prover space is
genuinely-approximate, genuinely-non-parity models, and the live attack is
`kun-block-transfer-lemma`.

## Attempts

- **Via the transfer lemma (open, primary).**  See
  `kun-block-transfer-lemma` and the route
  `two-point-fails-via-kun-blocks`; its own attack log records where each
  sub-mechanism stands, including the `Γ^h`-intertwining obstruction that
  killed the direct attempt.
- **Why not simply cite Kun--Thom (checked, does not apply).**
  `coordinate-action-not-sofic` refutes full-window injective equivariant
  charts; its argument consumes charts on every window element to build
  the size observable.  The two-point data carries one pair of labels and
  no injectivity anywhere else; the distinct_from notes of
  `two-point-orbit-approximation` already record that no implication
  between the statements is known.  Any use of the KT engine here must
  re-derive its strictness input from pair labels alone — that is
  attempt three of the transfer lemma, not a citation.
