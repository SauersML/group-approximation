---
rg: 2
id: invertible-ancilla-outputs-collapse-stable-formalization
kind: claim
title: A stable formalization whose identity-track outputs are formally right-invertible over the data yields a plain formalization
distinct_from:
  injective-binary-automata-are-stably-formalizable: that is the open universal stable target; this proves that every stable formalization of absorption type collapses to plain formalizability, so any proof of the target must use the identity tracks nonlinearly and recover them through the data output.
  formalizable-left-inverse-iff-clean-shear-dilation: that is the clean-ancilla equivalence on the original alphabet; this treats identity tracks read as inputs and shows that right-invertible identity-track outputs add nothing.
  sitewise-pairs-over-prime-fields-are-stably-formalizable: that constructs stable formalizations of sitewise pairs; this shows those constructions necessarily have relative ancilla maps with no formal right inverse, which makes this collapse sharp.
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `p` be prime, `G` a group, and `τ` an automaton on `(F_p^n)^G` with a left inverse. Suppose we
have a stable formalization of `τ` with `m` identity tracks:
- representatives `U(X, Y)` of the data output of `τ × id_m` and `V(X, Y) = Y + e(X, Y)`, where `e`
  vanishes on points;
- a left-inverse automaton `σ'` of `τ × id_m`, with a representative satisfying
  `σ~'(U, V) = (X, Y)` formally.

If the relative ancilla map `Φ(X, Y) = (X, V)` has an equivariant finite-memory formal right inverse
`Θ(X, Y') = (X, θ(X, Y'))`, then `U(X, θ(X, 0))` and `σ~'_X(·, 0)` are representatives of `τ` and of a
left inverse of `τ` whose composite is formally the identity. So `τ` has a plain formalization.

**Consequences.**
- **Additive absorption is dead.** If `e` depends only on the data, `θ = Y' − e(X)` works. Adding the
  Bennett remainder, or any data polynomial, into the identity tracks yields nothing beyond plain
  formalizability.
- **Directly finite hosts.** Suppose `M_(n+m)(F_p[G])` is directly finite. By
  `formal-polynomial-strict-pairs-need-unstable-linearization`, a finite-memory formal left inverse
  `(X, λ(X, V))` of `Φ` is a right inverse. In particular, if the ancilla recovery reads only `V`, the
  construction collapses.
- **The integers.** Take `G = Z` and `p = 2`, with any one-track `τ` that is not a translation composed
  with a complement, for instance the marker involution. Every stable formalization, with any number
  of identity tracks, has a relative ancilla map with no formal right inverse, and recovers the
  identity tracks through `U`. This uses `formalizable-binary-pairs-over-biorderable-groups-are-affine`,
  and direct finiteness of `M_N(F_2[Z])` via determinants.
- **Sharpness.** Non-affine sitewise permutations over `F_p`, `p >= 5`, are stably formalizable but
  not plainly formalizable. So their stable formalizations escape this collapse, and the escape class
  is nonempty.

Proof: Section 2 of the artifact.
