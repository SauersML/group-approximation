---
rg: 2
id: entanglement-sound-soundness-cannot-prove-ugc
kind: claim
title: No soundness analysis that also bounds entangled or commuting-operator strategies can prove UGC, and neither can a composition whose inner decoder handles entangled strategies
distinct_from:
  unique-games-entangled-value-approximable-by-sdp: that is the imported Kempe--Regev--Toner algorithm for the entangled value; this is its consequence for proof strategies, the precise gate every UGC reduction must pass (B2) and the two-layer composition kill (B3), neither of which is stated there.
  perfect-commuting-unique-game-is-classically-satisfiable: that is the zero-deficit collapse of perfect commuting strategies to labelings; this is the near-perfect regime, where entangled strategies of value 1-6eps exist on classically unsatisfiable NO instances.
  low-degree-view-unique-verifiers-collapse: that kills verifiers by the shape of their views (low-degree tests); this kills soundness proofs by the strategy class they quantify over, whatever the verifier.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that concerns linear-view verifiers collapsing to quotients; this is independent of the view structure and applies to any unique-game reduction.
artifacts:
  - research/artifacts/entanglement-sound-soundness-cannot-prove-ugc-proof-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts); it is not established because referees refuted the result as written. Write `val` for the classical value of a unique
game, `val*` for its entangled value (finite-dimensional tensor strategies, as in
`unique-games-entangled-value-approximable-by-sdp`) and `val_qc` for its
commuting-operator value, so `val <= val* <= val_qc <= omega_sdp1`. Fix
`eps, delta > 0` with `6 eps + delta < 1`. A reduction is a polynomial-time map
`R` from instances of a language `L` to unique games.

**B1 (entanglement-certified soundness decides the language).** Suppose
`x in L => val(R(x)) >= 1 - eps` and `x notin L => val_S(R(x)) <= delta`, where
`val_S` is `val*` or `val_qc`. Then `L in P`.

**B2 (the gate every UGC reduction must pass).** Assume `P != NP`. Let `R`
reduce an NP-complete `L` to `Gap-UG[1 - eps, delta]` with classical soundness
only. Then there are infinitely many NO instances `x` with
`val*(R(x)) >= 1 - 6 eps`, hence `omega_sdp1(R(x)) >= 1 - 6 eps`. So every proof
of UGC must, at its soundness step, use an inference that fails for
finite-dimensional entangled strategies on these instances.

**B3 (composition kill).** Let `O` map `L` to 2-to-1 games (or any label-cover
games), and let `R` map those to unique games with
`val(Psi) >= 1 - eta => val(R(Psi)) >= 1 - eps`. Consider two inner decoding
properties:

- `D_cl`: `val*(R(Psi)) > delta => val(Psi) > eta'`;
- `D_q`: `val*(R(Psi)) > delta => val*(Psi) > eta'`.

Then:

1. `D_cl` implies `D_q`.
2. `O` classically sound (`x notin L => val(O(x)) <= eta'`) together with `D_cl`
   gives `L in P`.
3. `O` entanglement-sound (`x notin L => val*(O(x)) <= eta'`, as in MIP*-style
   or rigidity-based outer PCPs) together with `D_q` gives `L in P`.

The same holds with `val_qc` replacing `val*` throughout.

**What dies, and where.** The killed class is every soundness analysis whose
conclusion bounds the value of all entangled strategies, or all commuting-operator
strategies, of the output unique game. Examples are:

- matrix-valued or noncommutative Fourier analysis and hypercontractivity;
- quantum low-individual-degree or rigidity tests used as the soundness engine;
- operator-algebraic (tracial, commuting-operator) decoding;
- and, by B3, any inner long-code decoder that decodes entangled strategies,
  either to classical labelings (`D_cl`) or to entangled strategies of the outer
  game composed with an entanglement-sound outer PCP (`D_q`).

Every member dies at the soundness inequality `val_S(R(x)) <= delta`. The
invariant is the SDP 1 value: it is at least `val_S` and certifies an entangled
strategy of value `1 - 6(1 - omega_sdp1)`. The only composition left open by B3
pairs a `D_q`-type decoder with outer instances whose classical value is small
but whose entangled value is large. There the decoder's conclusion says nothing
classical, so some later step must still use an inference invalid for entangled
strategies.

**Scope and credit.** B1 is essentially the authors' remark that the entangled
analogue of UGC is false; B2 and B3 recast it as a gate on proof techniques. An
explicit, unconditional instance for the binary folded noise test on fully rich
2-to-1 games is `clifford-long-codes-realize-pairing-value-in-binary-noise-test`.

A soundness analysis valid only for maximally entangled strategies with shared
randomness is not covered by the statement as proved. The KRT rounding
(Algorithm 1) has that form but uses unboundedly many copies, so the extension
needs a truncation argument, which is not written here.

## Attempts

- 2026-09-17 `swarm-0917` (ugc-pull-1): candidate direct proof, held OPEN. The route was withdrawn to `research/artifacts/entanglement-sound-soundness-cannot-prove-ugc-proof-2026-09-17.md`.
  Referee lens 1 returned *refuted*: B3 parts 2 and 3 use "x in L => val(O(x)) >= 1 - eta" and that `O` runs in polynomial time, but the B3 statement never assumes either (only `R` gets a completeness hypothesis); as written B3.2 is equivalent to P != NP (if P = NP, send every input to a fixed value-0 game and let `R` decide Gap-2to1 and output a fixed game, while `L` is outside P by the time hierarchy). Referee lens 2 returned *refuted*: the "dead as a class" bullet added to `rich-2to1-games-conjecture` overclaims, since KRT Theorems 1.3 and 4.5 need a unique game and KRT's only 2-to-1 result (Theorem 4.8) needs SDP value exactly 1; so nothing here rules out an entanglement-sound outer PCP to rich 2-to-1 games followed by the classically sound noise test, contradicting the claim's own "only composition left open" sentence. Lens 3 returned *survives* with the same missing-hypothesis caveat plus a midpoint-threshold remark for B1. All three lenses found B1, B2, the commuting-operator extension, C1--C4 and the KRT quotes sound, and `clifford_noise_test.py` passes.
