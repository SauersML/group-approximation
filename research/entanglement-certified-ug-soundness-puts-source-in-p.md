---
rg: 2
id: entanglement-certified-ug-soundness-puts-source-in-p
kind: claim
title: A polynomial-time complete reduction to unique games whose soundness bounds all entangled (or commuting-operator) strategies puts its source in P, so under P != NP every UG-hardness reduction, composed or not, has infinitely many NO outputs of entangled value at least 1 - 6 eps; entanglement-sound outer layers are left uncovered
distinct_from:
  entanglement-sound-soundness-cannot-prove-ugc: that is the earlier draft, refuted as written because its B3 omitted the completeness and polynomial-time hypotheses on the outer map O and its scope sentence overclaimed; this is the corrected statement, with every hypothesis explicit, the commuting-operator case reduced to the entangled case by val* <= val_qc, and a scope (E4) that leaves entanglement-sound outer PCPs followed by classically sound inner tests open.
  unique-games-entangled-value-approximable-by-sdp: that is the Kempe--Regev--Toner algorithm itself (held OPEN because of the draft above); this is its consequence for reductions, proved from the verbatim KRT quotes in its own route.
  perfect-commuting-unique-game-is-classically-satisfiable: that is the zero-deficit collapse of perfect commuting strategies; this is the near-perfect regime, where NO instances of entangled value at least 1 - 6 eps must exist.
  low-degree-view-unique-verifiers-collapse: that kills verifiers by the shape of their views; this kills soundness conclusions by the strategy class they quantify over, whatever the verifier.
  clifford-long-codes-realize-pairing-value-in-binary-noise-test: that (OPEN) proposes an explicit instance, for the binary folded noise test, of the entangled-value amplification that E4 shows every UG-hardness reduction must perform.
---

Notation. For a finite two-prover one-round game `G` write `val(G)` for its
classical value, `val*(G)` for its entangled value (the Kempe--Regev--Toner
limit over local dimension `d` of tensor strategies with projective
measurements) and `val_qc(G)` for its commuting-operator value. Then
`val <= val* <= val_qc` (deterministic strategies are dimension-one tensor
strategies; tensor strategies commute). A unique game is read as a two-prover
game by choosing a random constraint and randomly sending one endpoint to each
prover, as in KRT footnote 2. Fix constants `eps, delta > 0` with
`6 eps + delta < 1`. `L` is a language; every map below is computable in
polynomial time.

**E1 (entanglement-certified soundness decides the source).** Let `R` map
instances of `L` to unique games with

- completeness: `x in L => val(R(x)) >= 1 - eps`;
- `S`-soundness: `x notin L => val_S(R(x)) <= delta`, where `S` is `*` or `qc`.

Then `L in P`.

**E2 (the gate on classical reductions).** Assume `P != NP` and let `L` be
NP-hard. Let `R` satisfy the completeness of E1 and classical soundness
`x notin L => val(R(x)) <= delta`. Then there are infinitely many `x notin L`
with `val*(R(x)) >= 1 - 6 eps`, hence `omega_sdp1(R(x)) >= 1 - 6 eps`, while
`val(R(x)) <= delta`.

**E3 (compositions).** Let `O` map instances of `L` to finite two-prover games
(label cover, 2-to-1, ...) with outer completeness
`x in L => val(O(x)) >= 1 - eta`. Let `R` map games to unique games with inner
completeness `val(Psi) >= 1 - eta => val(R(Psi)) >= 1 - eps`. Consider, for
`Psi = O(x)` with `x notin L`, the inner decoding properties

- `D_cl`: `val*(R(Psi)) > delta => val(Psi) > eta'`;
- `D_q`: `val*(R(Psi)) > delta => val*(Psi) > eta'`.

Then:

1. `D_cl` together with classical outer soundness
   (`x notin L => val(O(x)) <= eta'`) gives `L in P`;
2. `D_q` together with entangled outer soundness
   (`x notin L => val*(O(x)) <= eta'`) gives `L in P`;
3. both hold with `val_qc` in place of `val*` in the decoder and in the outer
   soundness.

**E4 (exact scope: where entanglement must enter and where it may).** Assume
`P != NP`, `L` NP-hard, and let `R o O` be as in E3 with classical soundness
`x notin L => val(R(O(x))) <= delta`. Then there are infinitely many
`x notin L` with `val*(R(O(x))) >= 1 - 6 eps`. On these `x`:

- if `O` is classically sound, `val(O(x)) <= eta'`, so the inner map violates
  `D_cl` on them;
- if `O` is entanglement-sound, `val*(O(x)) <= eta'`, so the inner map violates
  `D_q` on them: `R` sends outer games of entangled value at most `eta'` to
  unique games of entangled value at least `1 - 6 eps`.

**What dies.** The killed class is every soundness analysis whose conclusion
bounds the entangled or commuting-operator value of the *output unique game*.
Examples are matrix-valued Fourier analysis or hypercontractivity applied to the
output game, quantum rigidity or low-individual-degree tests used as its
soundness engine, tracial or commuting-operator decoding, and inner long-code
decoders that decode entangled strategies (`D_cl` after any outer PCP, since
entanglement soundness implies classical soundness, or `D_q` after an
entanglement-sound outer PCP). Every member dies at the inequality
`val_S(R(x)) <= delta`. The invariant is the SDP 1 value: it bounds `val*`
from above, and on unique games its deficit is within a factor 6 of the
entangled deficit.

**What is not killed.** Entanglement soundness at the *outer* layer is allowed.
For example, an MIP*-style or rigidity-based outer PCP to rich 2-to-1 games
followed by a classically sound inner noise test is not covered by E1--E4.
KRT Theorems 1.3 and 4.5 concern unique games only, and KRT's one d-to-d statement (Theorem 4.8)
assumes `omega_sdp1(G) = 1` and gives only `omega*(G) >= 1/(20(d-1))`, which is
no approximation of the entangled value of near-perfect 2-to-1 games. E4 says
only what such a composition's inner test must do: amplify the entangled value from `eta'` to
`1 - 6 eps` on infinitely many outer NO images, as the OPEN node
`clifford-long-codes-realize-pairing-value-in-binary-noise-test` proposes to
exhibit explicitly for the binary test. Soundness analyses that hold only for
maximally entangled strategies with shared randomness are not covered.

## Attempts
