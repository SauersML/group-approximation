---
rg: 2
id: injective-binary-automata-are-stably-formalizable
kind: claim
title: Every injective binary automaton, after adding identity ancilla tracks, has a left inverse forming a formalizable pair
distinct_from:
  injective-binary-automata-have-formalizable-left-inverses: that asks for a formalizable left inverse on the original alphabet, which fails for one-track non-affine automata on bi-orderable groups; this allows identity ancilla tracks, where components reading the top cell can cancel and the leading-term obstruction no longer applies.
  binary-left-inverse-pairs-are-formalizable: that asks every pair on the original alphabet to be formalizable; this asks only for some left inverse of the stabilized automaton.
  sitewise-pairs-over-prime-fields-are-stably-formalizable: that treats sitewise pairs over prime fields; this asks for every injective binary automaton with arbitrary memory.
  prime-field-left-inverse-pairs-are-stably-formalizable: that is the prime-field form of stable formalizability, landed first by gk-fz-alphabets; this is the binary form that asks only for some left inverse of the stabilized automaton, which that claim implies at p = 2 and which already gives the binary Kaplansky payoff.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

**OPEN.** For every group `G` and every injective automaton `tau` on `(F_2^n)^G`, there is `m >= 0`
such that `tau x id` on `(F_2^(n+m))^G` has a left-inverse automaton `sigma'`, and representatives
of both with `sigma' o (tau x id) = id` formally. The representatives of the identity on the ancilla
tracks may involve data variables; only the functional identity is fixed.

**Why it matters.** `tau x id` is strict iff `tau` is. So by
`formal-polynomial-strict-pairs-need-unstable-linearization`, this claim makes every group with stably
finite `F_2[G]` surjunctive over every alphabet of size `2^n`, through
`stable-formalization-reduces-surjunctivity-to-kaplansky`.

## Attempts

- **One track is not enough.** Over bi-orderable groups a formalizable one-track binary pair is a
  shift plus a constant: the extreme variable enters `X_1` through one encoder component with degree
  `DE >= 1`, which forces single-cell windows. So the marker involution
  `x_i -> x_i + [x_(i-3..i+3) = 001*100]` on `{0,1}^Z` has no formalizable left inverse on its own
  alphabet (gk-fz-bennett). That refutes the unstabilized claims.
- **Tracks break that argument.** In the track shear `(x, y) -> (x, y + x(g+1) x(g+2))` the top
  variable cancels between components, and the pair is formalizable
  (`structurally-reversible-automata-are-formalizable`).
- **Sitewise pairs over prime fields** are stably formalizable
  (`sitewise-pairs-over-prime-fields-are-stably-formalizable`).
- **First test: the marker involution with one ancilla.** Compute the marker into the ancilla with a
  track shear, flip the data with a linear track shear, then uncompute. The uncompute leaves the
  residue `m_i(x + m(x)) - m_i(x)`. Markers are exclusive functionally, but `F_2[X]` is a domain,
  so `m_i m_(i+k)` is never zero formally, and the residue must be cancelled by other terms.
- **Regrouping decides the test case, but only after regrouping.** Along `4Z` the marker involution
  is the word `S_3 S_2 S_1 S_0` of track shears, one per residue class, with a formal inverse
  (`marker-involution-is-formalizable-after-regrouping`). That is a stabilization with the same
  Kaplansky payoff, but hosts without proper finite-index subgroups do not have it.
- **One ancilla, `Z`-equivariant word.** With `A : y += m(x)` and `B : x += y` applied in the order
  `A, B, A, B`, the output is `(x + m(x + y + m(x)), y + m(x) + m(x + y + m(x)))`. This is
  `tau x id` only when `y` does not disturb markers. The missing ingredient is a translation-invariant
  way to keep the controls fixed while the targets in the same track flip.
- **Parity is dead as an invariant.** Over `Z/2` with two tracks, a controlled square-zero affine map
  is a formal involution inducing an odd permutation (artifact, Section 6.5).
- **Boolean-adically the corrections always exist.** With an encoder representative whose reduced
  Jacobian is `I` at every Boolean point, every graded layer `I^k/I^(k+1)` is onto, so the decoder
  correction solves order by order (`binary-left-inverse-pairs-are-boolean-adically-formalizable`,
  gk-fz-obstruction). This applies verbatim to `tau x id`. So graded `I`-adic layers carry no
  invariant, and formalizability is exactly termination at finite degree and memory.
- **Any realization must be dirty at `y = 0`.** Let `(mu_1, mu_2)`, `(nu_1, nu_2)` be representatives
  realizing `tau x id` for the marker involution formally on `Z`. If `mu_2(x, 0) = 0` formally, then
  `(mu_1(., 0), nu_1(., 0))` is a formal one-track pair representing `tau`, which the one-track
  theorem of gk-fz-bennett forbids. So the ancilla component restricted to `y = 0` is a formally
  nonzero representative of `0`. The stable problem is genuinely weaker than a clean dilation, which
  is already refuted.
- **Two ways termination can fail** (gk-fz-obstruction). In finitely many variables the Boolean
  completion is `prod_c F_2[[X - c]]` over the Boolean points `c`. So non-termination is either
  unbounded memory of the corrections, or bounded memory with an infinite local power series at some
  Boolean point. Neither has been checked for `tau x id`.
- **Where it stops.** No `Z`-equivariant ancilla construction is known for the marker involution, and
  no invariant is known that survives cancellation between components. A negative answer must
  measure the growth in degree or memory of the corrections; a positive theorem must bound it.
