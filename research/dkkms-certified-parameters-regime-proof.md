---
rg: 2
id: dkkms-certified-parameters-regime-proof
kind: route
title: Proof that the inequalities of the DKKMS Lemma 5.3 soundness proof force the Theorem S regime at every certified parameter point
target: dkkms-certified-parameters-lie-in-the-selector-kill-regime
requires:
  - near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - two-to-two-games-theorem
artifacts:
  - experiments/ugc-dkkms-regime-closure-2026-09-17/check_dkkms_regime_closure.py
---

Notation is that of the target. `log` means either the natural or the base-2
logarithm. Both readings are handled, and nothing below depends on which one
is meant.

## Step 0. Verbatim source (ECCC TR16-198, Dinur--Khot--Kindler--Minzer--Safra)

The quotes are from the PDF text layer. Ligatures and sub/superscripts are
flattened, and the spacing has been normalised.

* **(D1) Choice of beta.** "β = log log k/k > 0."
* **(D2) Lemma 3.7, proof.** "Let r,q,C be from Hypothesis 3.6 for δ/2,
  ˜F = F. We prove the lemma for parameters r,q,C/2 and α(𝓁) = δ2^{−𝓁²−2}."
  Claim 3.8 then reads "At the end of the process, N > δ2^{−𝓁²−2}[n q]".
* **(D3) Lemma 3.17, proof.** "The first item follows immediately from
  Lemma 3.7, which relies on the main hypothesis".
* **(D4) Lemma 4.10.** "for at least 1−√βk^{1/4} fraction of Q,
  SD(L_Q,L′_Q) ⩽ √βk^{1/4}·2^{𝓁+5}. We call such subspaces Q smooth."
* **(D5) Lemma 5.3.** "For every δ > 0 there exists large enough 𝓁 ≪ k, such
  that given an assignment ˜A,B for G_folded that satisfies δ fraction of the
  constraints, there is an assignment for the 3LIN instance (X, Eq) that
  satisfies more than s∗ fraction of the equations."
* **(D6) Lemma 5.3, proof, parameters.** "Let C > 0, q, and r be the numbers
  promised in Lemma 3.17 for agreement δ²/2."
* **(D7) Lemma 5.3, proof, events.**
  - "1. Let E1 be the event that agreement(F_U) > δ²/4. Then Pr[E1] > δ/2."
  - "2. Let E2 be the event Q∈Gr(X_U,q) is smooth, namely (14) holds for Q.
    Then for every U, Pr[E2] > 1−√βk^{1/4}2^{𝓁+5} ≫ 1−α(𝓁)/2."
  - "3. Let E3 be the event that LIST_Q(F_U) ≠ φ. Then Pr[E3|E1] > α(𝓁)."
  - "Altogether this implies that Pr[E1∧E3] > δ/2·α(𝓁), and Pr[E1∧¬E2] ⩽
    δ/2·α(𝓁)/2 ⩽ δα(𝓁)/4 so Pr_{U,Q}[E1∧E2∧E3] > Pr[E1∧E3] − Pr[E1∧¬E2] >
    δα(𝓁)/4. (16)"
* **(D8) Lemma 5.3, proof, conclusion.** The proof shows a positive lower bound
  on "Pr [The players win|E1∧E2∧E3]" and continues "where all hidden constants
  may depend on δ and 𝓁 but are independent of k. So for large enough k this
  contradicts the soundness of Lemma 5.4."
* **(D9) Lemma 5.4** (quoted as (Q6) in `dkkms-selector-membership-proof`). The
  outer game has soundness `ε_k = exp(-k/exp(q l))`.

## Step 1. The two inequalities a certified point satisfies

Fix a DKKMS-certified point `(δ, l, k, q, r, C)`, meaning that the proof
(D5)–(D8) is valid at it. By (D6), (D3) and (D2), the `α(l)` of (D7) is the
`α` of Lemma 3.7 applied at agreement `δ1 = δ²/2`. Hence
`α(l) = δ1 2^(-l²-2) <= 2^(-l²-2)`.

**(P1).** The middle inequality of (16), `Pr[E1 ∧ ¬E2] <= δα/4`, is derived
from item 2 alone. Item 2 bounds `Pr_Q[¬E2 | U] <= X := √β k^(1/4) 2^(l+5)`
uniformly in `U`, and `E1` depends on `U` only. So the derivation gives
`Pr[E1 ∧ ¬E2] <= Pr[E1] X`. The only upper bound available on `Pr[E1]` is `1`,
since item 1 only bounds it from below. Therefore the step is valid only if
`X <= δα/4`, and in particular only if `X <= α/2`. This is also what item 2
asserts in words. Dropping the factor `2^(l+5) >= 1` leaves the weaker
inequality

```text
(P1)   sqrt(beta sqrt k) <= alpha(l)/2 <= 2^(-l²-3).
```

**(P2).** By (16) and (D8), the extracted outer strategy wins with probability
`> Pr[E1∧E2∧E3] · Pr[win | E1∧E2∧E3]`. The contradiction with Lemma 5.4 needs
this lower bound to exceed `ε_k`. The first factor is certified only as
`> δα/4`, and the second is at most `1`. So

```text
(P2)   eps_k < delta alpha(l)/4 <= 2^(-l²-4).
```

Both inequalities are strictly weaker than what the proof uses. The proof also
needs the factor `2^(l+5)` in (P1) and the list-size factor
`Pr[win | E1∧E2∧E3] < 1` in (P2). Using the weaker forms only enlarges the set
of points called certified, so Theorem C is stated for the larger set.

## Step 2. (P1) implies (R) for l >= 3

`k` is a positive integer and `β > 0` by (D1). With the natural log, this rules
out `k <= 2`. With the base-2 log, `β = 0` at `k = 2`, which also rules it out.
For `3 <= k <= 15`, `beta sqrt k = log log k / sqrt k >= 0.054` under both
readings (the minimum is `ln ln 3 / sqrt 3`). By (P1),
`beta sqrt k <= 2^(-2l²-6) <= 2^(-24)`, so `k >= 16`. For `k >= 16`,
`log log k >= 1` under both readings, so `1/sqrt k <= beta sqrt k`.

(P1) squared gives `beta sqrt k <= 2^(-2l²-6)`. Hence

```text
k >= 2^(4 l² + 12),
beta sqrt(k) 2^(l+3) <= 2^(-2l² + l - 3) <= 2^(-18)      (l >= 3),
3 * 2^(l-k) <= 3 * 2^(-2^(48)).
```

So `SD*(l,k) <= 2^(-18) + 3 * 2^(-2^48) < 3.82e-6 < 10^(-5)`, which is (R).

*Robustness in α.* Item 2 keeps the factor `2^(l+5)` and compares it with
`α/2`. Item 3 makes `α` a lower bound on a probability, so `α <= 1` whatever
proof supplies it. Hence `sqrt(beta sqrt k) 2^(l+5) <= 1/2`, so
`beta sqrt k <= 2^(-2l-12)` and `k >= 2^(4l+24)`. Then
`beta sqrt(k) 2^(l+3) <= 2^(-l-9) <= 2^(-17) < 7.7e-6` for `l >= 8`, and (R)
follows again. So the (R) half of Theorem C does not use the printed value of
`α` when `l >= 8`.

## Step 3. (P1) and (P2) imply (A) for l >= 5

* First half. `k >= 2^(4l²+12) >= l + 7`, so `2^(l-1-2k) <= 2^(-l-15) <= 1/16`.
* Second half. `p0²/4 = 2^(-2l) / (4 · 192²) = 2^(-2l - 2 - log2 36864)`.
  Since `log2 36864 < 15.17`, `p0²/4 > 2^(-2l-17.17)`. By (P2),
  `eps_k < 2^(-l²-4)`. So `eps_k <= p0²/4` as soon as
  `l² + 4 >= 2l + 17.17`, that is, `(l-1)² >= 14.17`, which holds for
  `l >= 5`.

Steps 2 and 3 give the first sentence of Theorem C.

## Step 4. Soundness below 1/16 forces l >= 6

In `G_folded(I)` each B-vertex `(V, L')` has label set `Fun(L')`, of size
`2^(l-1)`, and each constraint accepts exactly one B-label for a given class
label. Fix any class labelling and draw B-labels uniformly and independently.
Each constraint is then satisfied with probability `2^(1-l)`. So every
instance has value `>= 2^(1-l)`.

Suppose the reduction at the point sends some input, one whose 3LIN instance
has value `<= s*`, to a game of value `< δ`. Then `δ > 2^(1-l)`. If
`δ < 1/16` this gives `2^(1-l) < 2^(-4)`, so `l >= 6`.

A NO input exists unless the promise problem `Gap3Lin(1-eps_3, s*)` has an
empty NO side. In that case it lies in P, and its NP-hardness (DKKMS
Theorem 4.1) gives `NP = P ⊆ RP`. So under `NP not in RP`, which is the only
setting in which Corollary C1 says anything, the NO side is nonempty. This
proves the second sentence of Theorem C.

## Step 5. Corollaries

**C1.** Assume the hole with `eta'(eta) -> 0`, and assume `NP not in RP`.
Choose `eta < 1/16` with `eta'(eta) <= 10^(-5)`.

1. **Instances.** The hole defines `R_eta` as the reduction behind the 2-to-1
   form of `two-to-two-games-theorem`, and it names that reduction as the
   folded DKKMS Grassmann game. `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
   and Corollary S1 of Theorem S read it the same way. Its soundness is DKKMS
   Lemma 5.3 (D5). Lemma 5.3 is proved through Lemma 3.17 and Lemma 3.7 (D6,
   D3), from Hypothesis 3.6, which the later papers cited in
   `two-to-two-games-theorem` supply. So its parameter point is
   DKKMS-certified at soundness `δ = eta`.
2. **Regime.** By Step 4, `l >= 6`. By Steps 2 and 3, the point satisfies
   (R) and (A).
3. **Collapse.** Take the hole's orientation as the selector `S` of Theorem S,
   with `theta = 1`. The map `x -> I(x)` is the 3LIN part of `R_eta`. Its YES
   inputs have value `>= 1 - eps_3`, its NO inputs have value `<= s*`, and on
   YES inputs `val(U_o) >= 1 - eta' >= 1 - 10^(-5)`. Theorem S gives
   `Lang in RP` for an NP-hard `Lang`, so `NP in RP`. This contradicts the
   assumption.

Hence the hole implies `NP in RP`, with no parameter caveat. The two survivors
of Theorem S that concern DKKMS parameters, the `q = 1` window and the case
`q >= 2, l < 43`, contain no certified point with `l >= 5`. By Step 4, they
contain none with soundness below `1/16` at all.

**Scope of C1.** Theorem C concerns points certified by the proof as printed.
If the 2-to-2 chain certified `R_eta` by a different soundness argument, one
that does not pass through (16) and uses a much larger `α(l)`, the (A) half of
Step 3 would have to be redone. The (R) half would not, since Step 2's
robustness remark covers `l >= 8`. Every node in the graph that names the
proved instances already uses the reading of item 1. Item 1 also takes the
hole's own identification of `R_eta` with the DKKMS TR16-198 family. The hole
might be restated on the natively 2-to-2 A-A family of Khot--Minzer--Safra
(ECCC TR16-124), which is a live verifier concern. That family is outside
Theorem S, and C1 says nothing about it.

**C2.** The instances `D(I)` of
`parity-leaking-branch-selectors-reach-near-perfect-completeness` are the DKKMS
construction at a certified point, composed with a polynomial-time 3LIN map.
For these, Corollary S2 of Theorem S applies with the regime supplied by
Steps 2–4.

## Step 6. Numerical cross-check

The artifact scans `q = 1..12` and `l = 3..200` under both readings of
`log log`. For each pair it finds the least `k` with (P1) and (P2) at
`δ = δ1 = 1`, then tests (R) and (A). Since (P1), (P2), (R) and (A) are all
upward closed in `k` for `k >= 16`, the least `k` is the hardest case.

* The only failures are `q = 12, l = 3`, where (A) fails. That case lies
  outside Step 3's `l >= 5`.
* The largest `log2(beta sqrt k 2^(l+3))` is `-18.00`, which matches Step 2.
* For each of the 198 values of `l` where the `q = 1` window
  `k_A(l) <= k < k_0(l)` of Corollary S3 is nonempty, (P1) fails at its top
  end. Since (P1) is upward closed in `k`, it fails on the whole window.

The script prints `RESULT: PASS`.
