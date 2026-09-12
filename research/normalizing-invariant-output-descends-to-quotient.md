---
rg: 2
id: normalizing-invariant-output-descends-to-quotient
kind: claim
title: An invariant-output automaton whose memory normalizes its symmetry is a strict automaton on the quotient memory group
distinct_from:
  invariant-output-injective-automata-need-invisible-symmetry: that places the symmetry in the sofic radical of the memory group by permutation-model counting; this is an exact descent that turns the automaton itself into an injective non-surjective automaton on the quotient when the memory normalizes the symmetry.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Let `tau` be an injective cellular automaton over a group `G` with effective
memory `M`, output invariant under a finite subgroup `H != 1`
(`tau(x)(gh) = tau(x)(g)`), and `K = <M>`. If `M` normalizes `H`, then `H` is
normal in `K`, and the same local rule defines an injective, non-surjective
automaton over `K/H` with memory `{mH}`. So `K/H` is not surjunctive.

The automaton restricted to right-`H`-invariant configurations on `K` is that
quotient automaton. Its image `tau(Fix)` is a proper subset of
`tau(A^K)`, which lies in `Fix`.

**Consequence for the Leavitt design.** In `R^x = GL_2(R)`, the swap
`w = s0 t1 + s1 t0` has normalizer
`C(w) = R^x semidirect (R, +)`, the units of `R[eps]/(eps^2)`. A design with
`H = <w>` whose memory commutes with `w` is therefore a strict automaton on a
subgroup of `R^x semidirect (R / F_2 1)`: no easier than the problem it was meant
to solve. A candidate for `leavitt-units-carry-injective-invariant-output-automaton`
that genuinely uses its symmetry needs memory outside the normalizer. Only this
direction is proved. A strict automaton on the quotient does not yield an
invariant output, which would halve the information per coset. Proof: Section 2
of the artifact.
