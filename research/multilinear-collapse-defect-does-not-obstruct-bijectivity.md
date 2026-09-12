---
rg: 2
id: multilinear-collapse-defect-does-not-obstruct-bijectivity
kind: claim
title: The canonical multilinear chain-rule defect can be nonzero at a constant configuration for a sitewise reversible binary automaton
distinct_from:
  boolean-secants-do-not-supply-operator-left-inverses: that shows the Boolean function algebra has no Kähler differentials and that one involution has a singular telescoping secant; this computes the canonical multilinear Jacobians of a reversible pair at a constant configuration, where both are invertible over F_2[G] but their product is not the identity.
  formal-polynomial-strict-pairs-need-unstable-linearization: that shows a formal left-inverse identity forces bijectivity under direct finiteness; this shows even a reversible pair can fail to be formal in its canonical representatives, so the invariant to study is formalizability, not the multilinear defect.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Over the alphabet `F_2^3`, with coordinates `(a, b, c)`, let `T_1(a,b,c) = (a, b, c + ab)` and
`T_2(a,b,c) = (a + bc, b, c)` be Toffoli gates. Put `tau = T_2 o T_1` and `sigma = T_1 o T_2`,
acting sitewise (memory `{1}`) on `(F_2^3)^G` for any group `G`. They are mutually inverse
bijections.

**Canonical representatives.**
- Multilinear representatives: `tau = (a + ab + bc, b, c + ab)` and
  `sigma = (a + bc, b, c + ab + bc)`.
- Their formal composite is `(a + ab + ab^2, b, c + bc + b^2 c)`. It equals the identity on
  `{0,1}`-points only.

**At the constant configuration `(1,0,0)`.**
- `J_tau = [[1,1,0],[0,1,0],[0,1,1]]`.
- `tau(1,0,0) = (1,0,0)`, and `J_sigma(tau(1,0,0)) = [[1,0,0],[0,1,0],[0,1,1]]`.
- The product is `I + e_12`. So the collapse defect `D(c)` of
  `formal-polynomial-strict-pairs-need-unstable-linearization`'s artifact, Section 4, is nonzero,
  while both Jacobians are invertible and the pair is bijective.

**Consequences.**
- No invariant forces the canonical multilinear defect to vanish, on any group, including groups
  whose group algebras are stably finite. A route to "Kaplansky failure is necessary" through
  `D(c) = 0` is dead as stated.
- Linear parts of representatives are not invariants of the automata. Adding `(X_h^2 - X_h) P`
  to a rule changes its Jacobian at a Boolean constant configuration by `P(c)` at `h`.
- The representative-independent notion is **formalizability**: some representatives satisfy
  `sigma o tau = id` formally. This pair is formalizable, since the unreduced Toffoli composites
  compose formally to the identity. So it is a calibration, not a counterexample design.

Artifact, Section 6.
