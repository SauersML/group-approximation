---
rg: 2
id: two-point-approximation-fails
kind: claim
title: The two-point approximation fails at the marked pair — the negation claim
invalidates: [witness-yields-two-point-approximation]
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

## Resolution (2026-08-15, same day)

**ESTABLISHED**, via `two-point-fails-via-fixed-algebra`: the equivariance
clause hands over exact `Γ`-invariance of the `p`-label for free, a random
level set converts distinctness into a `Γ`-invariant projection that
`σ(h)` moves by `1/2`, the tensor-with-a-free-quotient repair makes the
assembled ultraproduct a genuine sofic representation covering even the
bounded-`|A|` provers, and Kun--Thom Theorem 4.1 (through
`normal-closure-fixes-gamma-fixed-algebra`) makes `h ∈ ⟨⟨Γ⟩⟩` act
trivially on the fixed algebra — contradiction.  Adversarially verified;
the one hole found in verification (the disjoint-union soficity repair
fails at bounded `|A|`, exactly where the flip models live) forced the
tensor repair now in the proof.

The earlier attempt log is retained below as the record of how the answer
was NOT found: the "why not simply cite Kun--Thom" reasoning was right
about `coordinate-action-not-sofic` (which localizes to no window) but
wrong to conclude the KT machinery could not be consumed — Theorem 4.1
sits upstream of that refutation and applies directly, precisely because
the two-point definition's own clauses re-derive the strictness input from
pair labels alone.

## Attempts (historical)

- **Via the transfer lemma (superseded).**  See
  `kun-block-transfer-lemma` and the route
  `two-point-fails-via-kun-blocks`; its attack log records the
  sheet-expansion program, including the `Γ^h`-intertwining obstruction.
  Superseded for this lane by the fixed-algebra route; retains value only
  for fixed-window quantitative versions, which the fixed-algebra route
  does not provide.
