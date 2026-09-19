---
rg: 2
id: entanglement-certified-ug-soundness-puts-source-in-p-krt
kind: route
title: Threshold the Kempe--Regev--Toner estimate of the entangled deficit, and compose
target: entanglement-certified-ug-soundness-puts-source-in-p
requires: []
---

**Import.** Julia Kempe, Oded Regev, Ben Toner, *Unique Games with Entangled
Provers are Easy*, arXiv:0710.0655v3 (FOCS 2008; SIAM J. Comput. 39(7), 2010).
The quotes were re-checked on 2026-09-19 against a text extraction of the arXiv
v3 PDF; spacing and symbols are normalized.

- (K1) Theorem 1.3 (p. 5): "There exists an efficient algorithm that, given a
  unique game whose entangled value is 1 - eps, outputs a value
  eps/6 <= eps' <= eps and a description of an entangled strategy for the
  provers whose success probability is at least 1 - 6 eps'."
- (K2) p. 5: "as long as, 6 eps + delta < 1, our algorithm can efficiently tell
  whether the entangled value of a game is at least 1 - eps or at most delta."
- (K3) Lemma 3.2 (p. 8): "Let G = G(pi, V) be a (not necessarily unique)
  one-round two-prover game. Then omega*(G) <= omega_sdp1(G)."
- (K5) Theorem 4.5 (p. 13): "Let G be a unique game. Suppose that
  omega_sdp1(G) = 1 - eps. Then omega*(G) >= 1 - 6 eps." Used only for the
  factor-6 invariant named in the claim; with (K3) it gives
  `1 - omega_sdp1 <= 1 - omega* <= 6 (1 - omega_sdp1)` on unique games.
- (K6) Footnote 2 (p. 6): "In order to derive a two-prover game from their
  construction, simply choose a random constraint and then randomly send one
  question to each prover." This fixes the reading of `val*` for constraint
  graphs.
- (K4) Theorem 4.8 (p. 15): "Let G be a d-to-d game for some d >= 2, and assume
  that omega_sdp1(G) = 1. Then omega*(G) >= 1/(20(d-1))." This is used only in
  the scope remark.

(K1) applies to every unique game, since every game has an entangled value
`1 - eps*` with `eps* in [0, 1]`; no promise is involved. We read "efficient" as
polynomial time on every input unique game.

**Elementary inequalities.** `val <= val* <= val_qc`:

- a deterministic classical strategy is a tensor strategy on `C^1 (x) C^1`, whose
  projectors are 0 or 1;
- a tensor strategy `A (x) I`, `I (x) B` is a commuting-operator strategy.

Write `A` for the KRT algorithm of (K1), and `T(G)` for "accept iff the output
`eps'` of `A` on `G` satisfies `eps' <= eps`". `T` runs in polynomial time on
every unique game.

**Lemma T.** Let `G` be a unique game with `val*(G) = 1 - eps*`.

1. If `val(G) >= 1 - eps`, then `T` accepts `G`.
2. If `val*(G) <= delta`, then `T` rejects `G`.
3. If `T` accepts `G`, then `val*(G) >= 1 - 6 eps` and `omega_sdp1(G) >= 1 - 6 eps`.

*Proof.*

1. `val* >= val >= 1 - eps`, so `eps* <= eps`, and (K1) gives `eps' <= eps* <= eps`.
2. `eps* >= 1 - delta`, and (K1) gives `eps' >= eps*/6 >= (1 - delta)/6`. This
   exceeds `eps` because `6 eps + delta < 1`.
3. `eps' <= eps`, and (K1) outputs a strategy of success probability at least
   `1 - 6 eps' >= 1 - 6 eps`, so `val*(G) >= 1 - 6 eps`. (K3) then gives the
   SDP bound.

(Parts 1 and 2 are exactly the authors' remark (K2).) QED

**E1.** The algorithm is: on input `x`, compute `G = R(x)` and output `T(G)`.
This runs in polynomial time, because `|R(x)|` is polynomial in `|x|` and `T`
is polynomial in `|G|`.

- If `x in L`, then completeness gives `val(G) >= 1 - eps`, and T.1 accepts.
- If `x notin L`, then `val*(G) <= val_S(G) <= delta`, using `val* <= val_qc`
  when `S = qc`, and T.2 rejects.

So `L in P`. QED

**E2.** Since `L` is NP-hard and `P != NP`, `L notin P`. Let `B` be the set of `x notin L` accepted by `T(R(x))`. By T.1 the algorithm
accepts every `x in L`, so it decides `L` except on `B`. If `B` were finite,
hard-coding `B` would put `L` in P, contradicting `P != NP`. So `B` is infinite.

By T.3, every `x in B` has `val*(R(x)) >= 1 - 6 eps` and
`omega_sdp1(R(x)) >= 1 - 6 eps`. Classical soundness gives `val(R(x)) <= delta`.
QED

(Using only (K2) with `delta' = 1 - 6 eps - gamma`, for `0 < gamma < 1 - 6 eps`,
the same patching argument gives infinitely many `x notin L` with
`val*(R(x)) > delta'`; this weaker form needs no quantitative part of (K1).)

**E3.** `R o O` runs in polynomial time, because `|O(x)|` is polynomial in `|x|`.
It is complete: if `x in L`, then `val(O(x)) >= 1 - eta`, so inner completeness
gives `val(R(O(x))) >= 1 - eps`.

1. Let `x notin L`. Classical outer soundness gives `val(O(x)) <= eta'`, so
   `D_cl` at `Psi = O(x)`, read contrapositively, gives `val*(R(O(x))) <= delta`.
   E1 with `S = *` applied to `R o O` gives `L in P`.
2. Let `x notin L`. Entangled outer soundness gives `val*(O(x)) <= eta'`, so
   `D_q`, read contrapositively, gives `val*(R(O(x))) <= delta`. E1 again gives
   `L in P`.
3. With `val_qc` in the decoder premise and conclusion (and in the outer
   soundness for part 2), the same contrapositives give
   `val_qc(R(O(x))) <= delta` for `x notin L`, and E1 with `S = qc` applies.
   The classical-conclusion decoder with a `val_qc` premise is covered by the
   same argument.

The hypotheses on `O` (polynomial time, outer completeness) are used exactly in
the first paragraph. Without them no unconditional proof is possible: referee
lens 1 on the draft `entanglement-sound-soundness-cannot-prove-ugc` shows that
the hypothesis-free form would imply P != NP. QED

**E4.** By the first paragraph of E3, `R o O` is a polynomial-time map with the
completeness of E1, and by hypothesis it is classically sound. E2 applied to
`R o O` gives infinitely many `x notin L` with `val*(R(O(x))) >= 1 - 6 eps`,
which exceeds `delta` since `6 eps + delta < 1`.

For such `x`, put `Psi = O(x)`. The premise `val*(R(Psi)) > delta` of both
decoders holds.

- If `O` is classically sound, then `val(Psi) <= eta'`, so the conclusion of
  `D_cl` fails.
- If `O` is entanglement-sound, then `val*(Psi) <= eta'`, so the conclusion of
  `D_q` fails.

QED

**Scope remark (not used above).** By (K4), KRT's d-to-d statement
needs `omega_sdp1 = 1` and gives an `omega*` bound depending on `d`, so nothing
imported here bounds the entangled value of near-perfect 2-to-1 outer games.
That is why E3.2 and E4 constrain only the inner map when the outer layer is
entanglement-sound, and do not rule out an entanglement-sound outer PCP followed
by a classically sound inner test.
