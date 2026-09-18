---
rg: 2
id: fg-groups-with-normal-q-n-have-non-fp-quotients
kind: claim
title: A finitely generated group with a normal subgroup isomorphic to Q^n acts on it through some GL_n(Z[1/m]), and its quotient by it is not finitely presented
distinct_from:
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that excludes linearly acting divisible subgroups from finitely-piecewise linear hosts; this is pure group theory about a normal copy of Q^n in an arbitrary finitely generated group.
  germ-extensions-omit-standard-gl-n-q: that concerns groups locally in a piecewise base off a nowhere dense set; this assumes no action on any space.
---

**ESTABLISHED (2026-09-17)** through `fg-groups-with-normal-q-n-have-non-fp-quotients-proof`.
Not independently reviewed. The argument is elementary and no priority is claimed; it is recorded as a
calibration obstruction for `gl-n-q-embeds-in-fp-simple-group`.

**Statement.** Let `n >= 1`, let `H` be a finitely generated group, and let `N ◁ H` be a normal subgroup with
`N ≅ (Q^n, +)`. Let `μ: H -> Aut(N) = GL_n(Q)` be the conjugation action. (Every additive automorphism of `Q^n`
is `Q`-linear, since `k f(x/k) = f(x)`.)

1. There is `m >= 1` with `μ(H) <= GL_n(Z[1/m])`. In particular `μ(H) ≠ GL_n(Q)`.
2. `H/N` is not finitely presented.

**Consequences for the root.**
- No finitely generated group `H` contains `Aff_n(Q) = Q^n ⋊ GL_n(Q)` with its translation subgroup normal in
  `H`: the conjugation image would contain all of `GL_n(Q)`, against part 1. Since
  `Aff_{n-1}(Q) <= GL_n(Q)` (matrices `[[g, v], [0, 1]]`), the same holds for the unipotent radical `Q^{n-1}` of
  that parabolic subgroup of `GL_n(Q)`, `n >= 2`.
- A host design in which a normal subgroup `N ≅ Q^n` supplies the divisibility of `GL_n(Q)` must have `H/N` not
  finitely presented. So "a divisible kernel over a finitely presented base" is impossible. The adelic covering
  `A^n -> (A/Q)^n` is the main instance: `adelic-deck-lifts-exclude-affine-q-n-and-fp-bases`.
- Part 2 does not forbid a finitely generated `H` with a normal (for instance central) copy of `Q^n`. It forbids
  a finitely presented quotient by it.
