---
rg: 2
id: normalizing-invariant-output-descends-to-quotient
kind: claim
title: An invariant-output automaton whose memory normalizes its symmetry is a strict automaton on the quotient memory group, and no injective one exists
distinct_from:
  invariant-output-symmetry-must-be-core-free: that forbids any nontrivial normal subgroup of the memory group inside the symmetry; this is the normalizing case, whose descent statement that filter shows to be vacuous.
  invariant-output-injective-automata-need-invisible-symmetry: that places the symmetry in the sofic radical of the memory group by permutation-model counting; this is an exact descent that turns the automaton itself into an injective non-surjective automaton on the quotient when the memory normalizes the symmetry.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `tau` be an injective cellular automaton over a group `G` with effective
memory `M`, output invariant under a finite subgroup `H != 1`
(`tau(x)(gh) = tau(x)(g)`), and `K = <M>`. If `M` normalizes `H`, then `H` is
normal in `K`, and the same local rule defines an injective, non-surjective
automaton over `K/H` with memory `{mH}`. So `K/H` is not surjunctive.

The automaton restricted to right-`H`-invariant configurations on `K` is that
quotient automaton. Its image `tau(Fix)` is a proper subset of
`tau(A^K)`, which lies in `Fix`.

**Sharper: the hypothesis is never met (2026-09-12).** If `M` normalizes `H`, then `H`
is normal in `K`. For `n in H` and `k in K`,

    tau(n^-1 . x)(k) = tau(x)(n k) = tau(x)(k (k^-1 n k)) = tau(x)(k),

so translation by `n` does not change the output on `A^K`, and injectivity forces
`n = 1`. So an injective automaton with right-`H`-invariant output, `H != 1`, never has
memory normalizing `H`, and the statement above is true but vacuous. This is the case
`N = H` of `invariant-output-symmetry-must-be-core-free` (gk-p-simple-direct).

**Consequence for the Leavitt design.** In `R^x = GL_2(R)`, the swap
`w = s0 t1 + s1 t0` has normalizer `C(w) = R^x semidirect (R, +)`, the units of
`R[eps]/(eps^2)`. A design with `H = <w>` whose memory commutes with `w` is not
injective at all. An earlier version said such designs are only as hard as a strict
automaton on `R^x semidirect (R / F_2 1)`. That reading is withdrawn. A candidate for
`leavitt-units-carry-injective-invariant-output-automaton` needs memory outside the
normalizer, and `<w>` core-free in the memory group. Proof: Section 2 of the artifact.
