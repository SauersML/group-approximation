---
rg: 2
id: selector-witness-hypotheses-collapse-to-selector-free-form
kind: claim
title: Every per-input structure hypothesis on constant-bias selector witnesses (such as Star-List^C for Theorem CLV), quantified over all selectors on a class P of YES inputs, is equivalent to its selector-free form "every orientation of lift value >= 1/2 + gamma on P satisfies it" unless no selector exists; with finitely many exceptions allowed it implies the selector-free form or P != NP; so the constant-bias kill of H1 through CLV reduces exactly to a selector-free list-decoding statement on an NP-hard sub-promise, and testability of P is irrelevant
distinct_from:
  star-list-structure-is-circular-on-decodable-yes-inputs: that is the special case P containing J-instances, where the selector-free form fails by Theorem O and the splice is by Gaussian elimination; this is the general collapse for every hypothesis and every class P, with a one-input hardcoding splice (exact form) and a Sigma_2 self-reduction splice under P = NP (asymptotic form), and it answers which restricted classes can work.
  value-free-star-list-references-put-np-in-rp: that proves Theorem CLV (Star-List^C implies RP); this shows its hypothesis, quantified over all selectors, can only be discharged by proving its selector-free form on the class.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this reduces the per-input-hypothesis kill programme for its constant-bias cell to one selector-free statement and leaves H1 open.
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is the open selector-free statement (SF) that this node reduces the kill to; this proves the reduction.
---

**ESTABLISHED** (Theorem X, Theorem A, Corollaries D, T and PNP'). Route:
`selector-witness-hypotheses-collapse-to-selector-free-form-proof`. Nothing
here is conditional on a complexity assumption. Theorem A and Corollary PNP'
are unconditional implications.

## Setting

Fix a doubled LEC `x -> D(x)` for a promise problem `Lang = (YES, NO)`, with
the notation of `value-free-star-list-references-put-np-in-rp`: the inner
2-to-1 game `G(x)`, orientations `o` of `G(x)`, and lifts `U_o`. Fix constants
`gamma > 0` and `theta(n) >= 1/poly(n)`.

* A **constant-bias selector** is a randomized polynomial-time algorithm `S`
  such that, on every YES input `x`, with probability `>= theta(|x|)`, the
  orientation `S(x)` has `val(U_(S(x))) >= 1/2 + gamma`. Write `sel` for
  "a constant-bias selector exists".
* A **witness hypothesis** is any predicate `Hyp(x, o)` on pairs of an input
  and an orientation. The main example is `Hyp = SL^C`: "there are a lift
  labelling `W` with `val(U_o, W) >= 1/2 + gamma` and a list `Lambda` of at
  most `L` arbitrary outer labellings with `D^C_L(proj W, Lambda) <= gamma - gamma'`".
* Let `P` be any set of YES inputs. It need not be decidable or testable.

Four statements:

* **U(Hyp, P).** For every constant-bias selector `S` and every `x in P`,
  `Pr[Hyp(x, S(x))] >= theta(|x|)`. This is the form in which Theorem CLV
  consumes a structure hypothesis, restricted to `P`.
* **U_inf(Hyp, P).** The same, for all but finitely many `x in P`. This is
  enough for CLV, since a decoder may hardcode finitely many answers.
* **F(Hyp, P)** (the *selector-free form*). For every `x in P` and every
  orientation `o` of `G(x)` with `val(U_o) >= 1/2 + gamma`, `Hyp(x, o)` holds.
* **F_inf(Hyp, P).** The same, for all but finitely many `x in P`.

A **violator** at `x` is an orientation `o` with `val(U_o) >= 1/2 + gamma` and
not `Hyp(x, o)`. So F fails exactly where a violator exists.

## Statements

**Theorem X (exact collapse).** For every witness hypothesis `Hyp` and every
set `P` of YES inputs,

```text
U(Hyp, P)   <=>   F(Hyp, P)  or  not sel.
```

Only the hypothesis's truth values are used. `Hyp` need not be decidable, and
`P` need not be testable.

**Lemma NP (Star-List^C is an NP relation).** Fix `gamma, gamma', L` and the
DKKMS parameters `(k, l, beta)`. Then `SL^C(x, o)` is in NP. A witness is
`(W, Lambda)`, of size `poly(|x|)`. The value `val(U_o, W)` and
`D^C_L(proj W, Lambda)` are exact rational averages over the explicit
poly-size supports of `mu` and `nu` in `D(x)`.

**Theorem A (asymptotic collapse).** Let `Hyp` be an NP relation. Then for
every `P`,

```text
U_inf(Hyp, P)   =>   F_inf(Hyp, P)  or  P != NP.
```

**Corollary PNP'.** If `F(Hyp, P)` fails, then `U(Hyp, P)` implies `P != NP`.
If `Hyp` is in NP and `F_inf(Hyp, P)` fails, then `U_inf(Hyp, P)` implies
`P != NP`. In each case the hypothesis can be proved only by an argument
that proves `P != NP`.

**Corollary D (the constant-bias kill, decomposed).** Let the instance
hypotheses of Theorem CLV ((E_tau) with `tau <= gamma'/4`, (M), (Bw), (M_B),
(S^C_L)) hold for `Lang`. Let `P` be a set of YES inputs such that the
promise problem `(P, NO)` is NP-hard under Karp reductions. Then

```text
F_inf(SL^C, P)   =>   ( sel  =>  NP subseteq RP ).
```

Conversely, by Theorems X and A, every proof of the premise of CLV in its
per-selector form `U_inf(SL^C, P)` proves `F_inf(SL^C, P)` or `P != NP`. So,
on every class `P`, the per-input structure route to the constant-bias cell
of H1 is exactly as strong as the selector-free statement

> **(SF_P)** for all but finitely many `x in P`, every orientation `o` of
> `G(x)` with `val(U_o) >= 1/2 + gamma` has a lift labelling `W` with
> `val(U_o, W) >= 1/2 + gamma` and a list of `<= L` arbitrary outer
> labellings with `D^C_L(proj W, Lambda) <= gamma - gamma'`.

This is `good-dkkms-orientations-admit-short-star-lists-on-hard-inputs` (OPEN).

**Corollary T (every per-input hypothesis on the ladder).** Theorem X applies
verbatim, with no condition, to each per-selector witness hypothesis used so
far for the constant-bias cell: List-Seed, List-Str_t, the Star-List
hypothesis of Theorem CL, and (Star-List^C). Quantified over all selectors,
each one is equivalent to its selector-free form or to `not sel`. Theorem A
applies to each one that is an NP relation. By the argument of Lemma NP, that
includes every list hypothesis whose list length is `O(1)` in `|x|` and whose
charge is an explicit average over the instance's supports.

**Answer to need 8842dd02** ("a class of YES inputs that the decoder can
test"). Testability, decodability and non-decodability of `P` play no role.
If `F(Hyp, P)` fails, the restricted hypothesis `U(Hyp, P)` implies
`P != NP` (Corollary PNP'). Whether `F(Hyp, P)` fails is a combinatorial
property of the instances in `P` alone. Take the parameter range of Theorem
O of `star-list-structure-is-circular-on-decodable-yes-inputs`:
`2^(2-l) <= gamma' < gamma <= 0.105` and `L <= gamma'^2 2^(k-l-16)`. There,
if `P` contains even one J-instance, `F(SL^C, P)` fails, since its flip
orientation `o*` is a violator. So
the exact form dies by hardcoding that one instance, without Gaussian
elimination. The asymptotic form dies once `P` contains infinitely many
J-instances. The only live question for a class `P` is (SF_P).

## What it kills (impact types 2 and 3)

**Class.** Routes to the constant-bias cell of H1 of the form "every
constant-bias selector's output, on every (or almost every) input of a class
`P`, satisfies a per-input witness hypothesis `Hyp(x, o)`; then a decoder in
the style of CLV decides `(P, NO)`". This covers the restrictions of P that
need 8842dd02 proposed, and every future hypothesis of the same per-input
shape, whatever the decoder.

**Invariant.** The violator set `Viol_Hyp(x)`, the good orientations of `G(x)`
that fail `Hyp`. This set is defined without reference to any selector.

**Step where every member dies.** The per-selector hypothesis, applied to the
patched selector `S'`. `S'` agrees with `S` except on inputs with a violator,
where it outputs one. For the exact form, one input with a violator is enough.
For the almost-every form under P = NP, `S'` is computed in polynomial time by
Sigma_2 self-reduction.

When `Viol` is nonempty on `P` (or infinite on `P`, for the asymptotic form),
the hypothesis is equivalent to the conclusion `not sel`, or implies
`P != NP`. When `Viol` is empty (or finite) on `P`, the hypothesis holds for
every good orientation, and nothing about `S` is used beyond its bias. Either way, a hypothesis about selector witnesses carries no
information beyond the selector-free statement (SF_P). The route's whole
content is the list decoding of good orientations of `G(x)`, a question about
the 2-to-1 test and not about algorithms.

**Consequence.** The constant-bias kill programme for H1 through CLV now has
exactly one open prerequisite: (SF_P) for some NP-hard sub-promise `P`. The
prerequisite is `good-dkkms-orientations-admit-short-star-lists-on-hard-inputs`.
It can fail on its own, and it is already known to fail for any `P` that
contains J-instances (Theorem O).

## What survives

* **Global or cross-input hypotheses.** Examples are "`S(x)` and `S(x')` are
  related when `x, x'` are neighbouring inputs for most pairs", or bounds on
  the circuit size of `S`. A finite patch moves these only on a vanishing
  fraction of pairs. A patch under P = NP can break them.
* **Average-case hypotheses.** "`Pr_(x ~ D_n)[Hyp(x, S(x))] >= theta`" for a
  samplable, spread-out `D_n`. The exact collapse fails here, because a
  finite patch changes the measure by `o(1)`. The collapse under P = NP still
  applies, with `F` in its average form. Even so, CLV then decides only an
  average-case version of `Lang`.
* **Decoders that use `S` as an oracle on inputs other than `x`**, such as
  self-reducibility-style queries on modified instances. Their hypothesis is
  not per-input.
* **Proving (SF_P) outright** on a kernel-free sub-promise. This is the
  decomposition above, not a survivor of the kill.
