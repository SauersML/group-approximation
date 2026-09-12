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
- **Right-invertible ancilla outputs collapse** (gk-fz-strict,
  `invertible-ancilla-outputs-collapse-stable-formalization`).
  - **The collapse.** Suppose `(X, Y) -> (X, Y + e)` has a finite-memory formal right inverse
    `(X, θ(X, Y'))`. Substituting `Y = θ(X, Y')` and then `Y' = 0` gives a plain formalization.
  - **Absorption is dead.** Adding the Bennett remainder, or any data polynomial, into the identity
    tracks never works.
  - **Directly finite hosts.** If `M_(n+m)(F_2[G])` is directly finite, recovering the identity tracks
    from `V` alone collapses too.
  - **The marker involution over `Z`.** Every stable realization must recover the identity tracks
    through the data output, nonlinearly. The dirty-at-`y = 0` entry above is the case where `θ` is
    the identity.
  - **Calibrations.** Output-only extra tracks always formalize but certify nothing
    (`garbage-output-tracks-formalize-every-left-inverse-pair`).
  - **Erasure.** No sitewise gate clears a nonlocal remainder onto a clean track
    (`sitewise-gates-cannot-erase-nonlocal-defects`). That applies on hosts without proper
    finite-index subgroups, since regrouping escapes it.
- **Where it stops.** No `Z`-equivariant ancilla construction is known for the marker involution, and
  no invariant is known that survives cancellation between components. A negative answer must
  measure the growth in degree or memory of the corrections; a positive theorem must bound it.
- **What termination means for the stabilized pair (gk-fz-catalyst; corrected after gk-vf-nonlinear,
  Section 33 of its verification artifact).** By Theorem 5 of
  `formalizability-is-a-boolean-ideal-cokernel-class`, with a Lemma C encoder representative every
  graded layer of the correction problem for `tau x id` is solvable by equivariant finite-memory
  `delta_k`, each extended under the full group `G`, so every layer is already `G`-invariant. The
  solution is unique only when the encoder is bijective. For strict `tau` the layer maps are onto
  but not injective, so there are choices. Formalizability of the stabilized pair is the
  **existence of some choice** whose series terminates: finite degree and finite total memory.
- **Regrouping relaxes equivariance, not termination.** Regrouping along a finite-index `H <= G`
  keeps the variables `X_g` and asks only for `H`-equivariant finite-memory representatives on the
  regrouped alphabet. `marker-involution-is-formalizable-after-regrouping` is such a formalization
  with `H = 4Z`, one track shear per residue class mod 4. So over `Z` the marker involution already
  has a terminating formalization with `4Z`-equivariant representatives, and the ancilla question is
  whether identity tracks let a `Z`-equivariant one exist. The regrouped solution does not decide
  that either way.
- **Where a proof must live.** A negative answer over `Z` must obstruct `Z`-equivariant
  representatives with identity tracks while not obstructing the `4Z`-equivariant formalization,
  for instance a multi-track generalization of gk-fz-bennett's one-track Theorem A
  (`formalizable-binary-pairs-over-biorderable-groups-are-affine`); identity tracks defeat its naive
  extension through cancellation between components. A positive answer must exhibit a terminating
  `G`-equivariant catalytic word: data output `Y`-free on points (forced by `U = tau(X)` for all
  `Y`), ancilla offset a nonzero element of `I` recovered through the data output.
- **Scope: the load-bearing test object is not on `Z` (gk-fz-catalyst).** The Kaplansky payoff is
  needed on finitely generated simple hosts (`gottschalk-reduces-to-fg-simple-kazhdan-groups`), which
  have no proper finite-index subgroup, so regrouping is unavailable and only `G`-equivariant
  representatives exist. The marker involution lives on `Z`, which has finite-index subgroups, so it
  is a warm-up whose regroup-formalizability already yields the payoff over `Z`. The genuine open
  ancilla test object is a reversible binary cellular automaton over a finitely generated simple
  group (for instance a first-letter-swap involution inside Thompson's `V` or the Leavitt unit group
  acting on Cantor space); none is on record.
- **Finitely generated simple hosts (w3-stable-simple, 47275abc1f and cee710f2ff).**
  - **No refutation reaches them.** No nontrivial finitely generated simple group is bi-orderable
    (`finitely-generated-simple-groups-are-not-biorderable`). So one-track affine rigidity, and with it
    the marker refutations over `Z` and `Q`, never apply there, not even at one track. Formal pairs push
    forward only along quotients of the encoder memory group
    (`formal-pairs-push-along-quotients-of-the-encoder-memory-group`), and that is void once the memory
    generates the simple host.
  - **One track already has room.** Hosts with a non-central involution, including `V` and
    `L_(F_2)(1,2)^x`, carry non-affine one-track formal involutions
    (`non-central-involutions-carry-nonaffine-formal-involutions`, built from zero-divisor shears in
    `zero-divisor-shears-are-formal-automorphisms`).
  - **A restricted plain target is live.** `binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable`
    needs no ancilla. It already gives the per-host Kaplansky payoff through
    `simple-host-formalization-reduces-surjunctivity-to-kaplansky`.
  - **First test objects.** The marker involution along an infinite-order dihedral element of `V`
    (`thompson-v-marker-involution-is-formalizable`), and its dihedral core, which is `tau_Z x tau_Z`
    over `Z` with reflection symmetry (`dihedral-marker-involution-is-formalizable`).
  - **What gates cannot do.** For strict `tau`, a formal pair has a surjective, non-injective encoder
    pullback, so no word in formal automorphisms supplies it.
