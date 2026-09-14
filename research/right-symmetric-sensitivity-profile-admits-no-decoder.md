---
rg: 2
id: right-symmetric-sensitivity-profile-admits-no-decoder
kind: claim
title: An automaton whose single-site sensitivity profile has a right symmetry of order divisible by the alphabet size has no left inverse
distinct_from:
  invariant-output-automata-have-only-nonlinear-decoders: that excludes linear decoders by augmentation; this excludes decoders of every degree whenever the encoder's single-site sensitivity profile is right-invariant under an element of order divisible by the alphabet size.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Let `G` be any group, `A = Z/n`, and `tau(x)(g) = f((x(gm))_(m in M))`. For
`b != 0`, put `p_b(m) = f(b e_m) - f(0)` for `m in M` and `p_b = 0` off `M`, where
`b e_m` is `b` at `m` and `0` elsewhere. If `sigma tau = id` for some automaton
`sigma`, then no `p_b` is invariant under right multiplication by an element
whose order is divisible by `n`.

*Why.* `tau(b e_k) = f(0) + p_b(. ^-1 k)`. The decoder must return `b` at `1`
exactly for `k = 1`, so the finite sum over `k` of the decoded change at `1` is
`b`. A right symmetry `c` of `p_b` makes that change constant on right
`<c>`-orbits, each of size `ord(c)`, so the sum is `0` in `Z/n`.

**Consequence.** Over `F_2` the linear support of an encoder with a left inverse
has no right symmetry of even order. An invariant-output encoder whose linear
part is one orbit `k + hk` is right-invariant under `k^-1 h k`, so it has no
decoder of any degree. A candidate for
`leavitt-units-carry-injective-invariant-output-automaton` needs linear support
spread over at least two left orbits. Proof: Section 4 of the artifact.
