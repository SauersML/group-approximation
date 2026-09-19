---
rg: 2
id: selector-witness-hypotheses-collapse-to-selector-free-form-proof
kind: route
title: Patch any constant-bias selector at inputs carrying a violator -- by hardcoding one input for the exact form, and by Sigma_2 self-reduction under P = NP for the almost-every form -- so a per-selector witness hypothesis can hold only where its selector-free form does
target: selector-witness-hypotheses-collapse-to-selector-free-form
requires:
  - star-list-structure-is-circular-on-decodable-yes-inputs
  - value-free-star-list-references-put-np-in-rp
---

The notation is that of the target.

## Theorem X

*(F or not sel) implies U.* If `not sel`, then `U(Hyp, P)` is vacuous. If
`F(Hyp, P)` holds, fix a selector `S` and `x in P`. Every outcome of the coins
with `val(U_(S(x))) >= 1/2 + gamma` has `Hyp(x, S(x))`, by F. So
`Pr[Hyp(x, S(x))] >= Pr[val(U_(S(x))) >= 1/2 + gamma] >= theta(|x|)`.

*U implies (F or not sel).* Suppose `sel` holds, witnessed by `S`, and F
fails. Then there are `x_0 in P` and a violator `o_0` at `x_0`. Define

```text
S'(x) := o_0     if x = x_0,
S'(x) := S(x)    otherwise.
```

`S'` is a randomized polynomial-time algorithm: a fixed machine that compares
its input with the constant string `x_0`. It is a constant-bias selector. At
`x_0` it outputs `o_0` with probability 1, and `val(U_(o_0)) >= 1/2 + gamma`.
On every other YES input it is `S`. But `Pr[Hyp(x_0, S'(x_0))] = 0 < theta`,
so `U(Hyp, P)` fails at `(S', x_0)`. Nothing about `Hyp` or `P` was used
beyond truth values.

## Lemma NP

An orientation `o` of `G(x)` names one preferred preimage per constraint, so
it is a string of length `poly(|x|)`. The lift `U_o`, the constraint law `mu`
and the star law `nu` of `D(x)` have explicit poly-size supports with rational
weights. A witness for `SL^C(x, o)` is a lift labelling `W` together with `L`
outer labellings `lambda^1, ..., lambda^L`, where `L` is a constant in `|x|`.

The verifier does three things:

* computes `val(U_o, W)` exactly;
* computes `proj W = H`, and, for each constraint `e` in `Sat(H)` and each
  `j`, whether `e in X^C(H, lambda^j)`. This membership is given by the
  annotation `ev_e` and the outer constraint `pi_(a_e b_e)`, following the
  definition of `X^C` in `value-free-star-list-references-put-np-in-rp`;
* computes `D^C_L(H, Lambda) = E_((w,a) ~ nu) min_j mu(X^C(H, lambda^j) | w, a)`
  exactly, as a finite sum.

All of this takes `poly(|x|)` time for fixed `(k, l, beta, L)`.

## Theorem A

Assume `P = NP`. We show that `U_inf(Hyp, P)` implies `F_inf(Hyp, P)`.

**(a) A selector exists.** This is Corollary PNP of
`star-list-structure-is-circular-on-decodable-yes-inputs`, verbatim: "If
P = NP, a constant-bias selector exists. It finds a labelling `H` of `G(x)`
with `val_G(H) >= 1/2 + gamma` by self-reduction, and orients each
constraint by `pref_e := H`'s A-label." Call it `S`.

**(b) Violators are found in polynomial time.** Put
`V(x, o) := [exists W : val(U_o, W) >= 1/2 + gamma] and not Hyp(x, o)`.
The first conjunct is in NP. The second is in coNP, since `Hyp` is an NP
relation. Under `P = NP` both are in P, so `V` is in P. Now let
`E := {(x, p) : exists o extending the prefix p with V(x, o)}`. Since the
lengths of `o` are polynomially bounded and `V` is in P, `E` is in NP, and
hence in P. Prefix search over `E` finds a violator `o_x`, bit by bit, in
deterministic polynomial time whenever `(x, empty) in E`. This is the
standard collapse `Sigma_2^p = P` under `P = NP`, together with
search-to-decision.

**(c) Patch.** Define `S'(x) := o_x` when `(x, empty) in E`, and
`S'(x) := S(x)` otherwise. `S'` runs in polynomial time. It is a
constant-bias selector: on a YES input where a violator exists, it outputs
`o_x` with probability 1, and `val(U_(o_x)) >= 1/2 + gamma`; elsewhere it is
`S`. Membership in `P` is never tested.

**(d) Conclusion.** Suppose `F_inf(Hyp, P)` fails. Then infinitely many
`x in P` carry a violator. At each of them `Pr[Hyp(x, S'(x))] = 0`, so
`U_inf(Hyp, P)` fails at `S'`. By contraposition, `U_inf` and `P = NP`
together imply `F_inf`.

## Corollary PNP'

* *Exact form.* If `F(Hyp, P)` fails, Theorem X turns `U(Hyp, P)` into
  `not sel`. By (a), `not sel` implies `P != NP`.
* *Asymptotic form.* This is Theorem A with `F_inf` false.

## Corollary D

Assume `F_inf(SL^C, P)`, and let `S` be a constant-bias selector. Let `E_0` be
the finite set of exceptions, and put `P_0 := P minus E_0`. By the first half
of Theorem X, applied to `P_0`, `Pr[SL^C(x, S(x))] >= theta(|x|)` on every
`x in P_0`.

This is the hypothesis of Theorem CLV (`value-free-star-list-references-put-np-in-rp`)
for the promise problem `Lang_0 := (P_0, NO)`. Its instance hypotheses (E_tau),
(M), (Bw), (M_B) and (S^C_L) are conditions on the instances `D(x)` for YES
and NO inputs, so they pass to the sub-promise. Theorem CLV gives
`Lang_0 in RP`.

`(P, NO)` differs from `Lang_0` on the finite set `E_0` of YES inputs.
Hardcoding acceptance on `E_0` gives `(P, NO) in RP`. Compose any Karp
reduction from an NP-complete language to `(P, NO)` with this one-sided
algorithm, and the result is `NP subseteq RP`.

The converse sentence of Corollary D is Theorems X and A, applied with
`Hyp = SL^C`, which is an NP relation by Lemma NP.

## Corollary T

Theorem X used only the truth values of `Hyp`, so it applies to every
per-selector witness hypothesis. Theorem A used only that `Hyp` is an NP
relation. The proof of Lemma NP covers any list hypothesis whose witness is a
labelling plus `O(1)` references, charged by an explicit average over the
supports of `D(x)`.

## Answer to need 8842dd02

Fix the parameters of Corollary CIRC of
`star-list-structure-is-circular-on-decodable-yes-inputs`:
`l >= 8`, `2^(2-l) <= gamma' < gamma <= 0.105`, `L <= gamma'^2 2^(k-l-16)`,
rank `n = k - c`, and `k` large. Let `x_J` be a J-instance with `>= k` copies.
That node's proof of CIRC gives two things:

* `o*` has a lift labelling of value `>= 0.605 >= 1/2 + gamma`;
* every `W'` with value `>= 1/2 + gamma` has `D^C_L >= gamma - E > gamma - gamma'`
  (Theorem O item 2).

So `o*` is a violator of `SL^C` at `x_J`.

If `P` contains `x_J`, then `F(SL^C, P)` fails, and Theorem X hardcodes
`(x_J, o*)`. If `P` contains infinitely many J-instances, then
`F_inf(SL^C, P)` fails, and Theorem A applies. Neither step asks whether `P`
is testable, decodable or non-decodable. Those properties enter only through
whether `P` contains violators, which is the content of (SF_P).
