---
rg: 2
id: efficient-branch-selectors-list-decode-honest-outer-labels
kind: claim
title: A polynomial-time branch selector whose orientation lift of a linearly encoded composed 2-to-2 or 2-to-1 instance gives some honest labelling value 1/2 + gamma yields a Fourier list decoder of outer labels, so NP is in RP; above one half honest completeness is NP-collapse-hard and tight
distinct_from:
  unique-constraints-orient-at-most-half-of-a-fiber: that is the unconditional injectivity wall for local unique-constraint gadgets at perfect completeness; this covers every polynomial-time selector, however global or parity-leaking its view, at every completeness above 1/2, and is conditional on NP not in RP, which is unavoidable because P = NP makes such selectors exist.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that covers verifiers whose views are affine in the outer label, unconditionally; this allows an arbitrary polynomial-time computation of the branch bits and gets its obstruction from list decoding, not from the view structure.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that uses perfect completeness to solve a computable skeleton; this is silent about skeletons, works at completeness 1/2 + gamma, and decodes outer labels from branch-bit advantage.
  unique-games-hard-at-completeness-one-half: that is the split reduction, whose honest completeness is exactly 1/2; this shows no efficient choice of branches pushes honest completeness above 1/2 unless NP is in RP.
artifacts:
  - experiments/ugc-selector-decoding-2026-09-17/check_selector_decoding.py
---

**ESTABLISHED.** This is a class kill for the branch-selector completeness
step. It is conditional on `NP not in RP`, and that condition cannot be
removed (Theorem 2).

## Setting

**Composed instances.** A *linearly encoded composition* (LEC) with parameters
`(l, m, tau, K)` is a polynomial-time map `R` from strings `x` to the following
data, together with its run.

1. **Outer game.** A projection game `Phi = (A, B, rho, pi)`.
   - `rho` is a distribution on edges `(a,b)` in `A x B`.
   - The `A`-labels lie in `F_2^m`, where `2^m` is polynomial in `|x|`.
   - Each `pi_ab` maps `A`-labels to `B`-labels.
   - An outer labelling `lambda` has value
     `val_Phi(lambda) = Pr_(a,b)~rho [pi_ab(lambda_a) = lambda_b]`.
2. **Inner game.** A game `G` with vertex set `V_G` and label sets `Sigma_w`,
   where `|Sigma_w| <= 2^l`, and a distribution `mu` on constraints. Each
   constraint is 2-to-2 or 2-to-1, as in `two-to-two-games-theorem`.
3. **Honest encoding.** A map `hon` from outer labellings to labellings of `G`.
4. **Edge annotations.** Each constraint `e` has a *seed* endpoint `w_e` in
   `V_G`, a *target* outer vertex `a_e` in `A`, and a *direction* `x_e` in
   `F_2^m`.

**Selectors and lifts.** An *orientation* of `e` picks one perfect matching
inside every `K_(2,2)` block of a 2-to-2 constraint, or one preimage per fiber
of a 2-to-1 constraint. A *branch selector* is a choice of orientation for every
constraint. Its *bit function* `g_e : Sigma_(w_e) -> F_2` records, for each
seed label `s`, the value at the direction `x_e` of the label that the
orientation attaches to `s`. Theorem 1 uses only that `g_e` is some function.
Theorem 2 only needs to prescribe `g_e` at one label per block, which an
orientation can always do. The *orientation lift* `G_g` is the unique game
with the oriented constraints. Each oriented constraint is a bijection, and the
artifact checks this. It uses exactly one of the two fiber elements, as
`unique-constraints-orient-at-most-half-of-a-fiber` forces. Every oriented
constraint is contained in the original one, so `val(G_g) <= val(G)`, and
soundness transfers for free.

**Hypotheses on an LEC.**

* **(B) branch identity.** For every `lambda`, `g` and `e`: if `hon(lambda)`
  satisfies the oriented constraint of `e` in `G_g`, then
  `g_e(hon(lambda)_(w_e)) = <lambda_(a_e), x_e>`.
  - **(B+)**, the converse, also holds: if `hon(lambda)` satisfies `e` in `G`
    and the prediction is correct, then it satisfies the oriented constraint.
  - For Grassmann constraints, (B+) is exhaustively checked by the artifact for
    `m = 4, l = 2`. The constraints checked are 2-to-2 between `L_0` and `L_1`
    with `dim(L_0 cap L_1) = l - 1`, and 2-to-1 restrictions `L_0 -> H`.
  - In both cases the orientation bit is `s(x_0) xor g(s|H)` and the honest
    branch is `<sigma, x_1>`, resp. `<sigma, x_0>`. The known part `s(x_0)` is
    absorbed into `g_e`.
* **(E) uniform directions.** For every `(w,a)` in the support of `(w_e, a_e)`
  under `mu`, the conditional law `D_(w,a)` of `x_e` is within total variation
  `tau` of uniform on `F_2^m`.
* **(M) marginal comparability.** Let `nu_A` be the law of `a_e` under `mu`,
  and `rho_A` the law of the `A`-endpoint under `rho`. Then
  `nu_A(a) <= K rho_A(a)` for every `a`.

**Honest completeness.** A selector algorithm `S` is randomized polynomial
time; it reads `x`, the run of `R`, and `G`, and outputs `g`. It has *honest
completeness `1/2 + gamma` with confidence `theta`* on a language `Lang` if the
following holds for every `x` in `Lang`. With probability `>= theta` over the
coins of `S`, there is an outer labelling `lambda` such that:

* `val_Phi(lambda) >= 1 - eps`;
* `val_(G_g)(hon(lambda)) >= 1/2 + gamma`.

## Statements

**Theorem 1 (selectors decode).** Let `R` be an LEC satisfying (B), (E) and
(M) with `tau <= gamma/4`. Put

```text
p  = gamma^3 2^(-l-2),        c0 = p^2 / K^2 - 2 eps.
```

Suppose that:

* `x in Lang` implies that `Phi` has a labelling of value `>= 1 - eps`;
* `x notin Lang` implies `val(Phi) <= s`, with `s < c0/2`;
* a selector `S` has honest completeness `1/2 + gamma` with confidence `theta`.

Then `Lang in RP`, with one-sided success probability `>= theta c0/2` per
trial. In particular, if `Lang` is NP-hard, then `NP in RP`.

**Corollary (the one-half wall is computational).** Assume `NP not in RP`, and
take an LEC family from an NP-hard gap label cover with `tau <= gamma/4` and
`2 eps + 2 s < p^2/K^2`. Then no polynomial-time selector gives an honest
labelling of an outer labelling with value `>= 1 - eps` an orientation-lift
value `>= 1/2 + gamma`.

Near-honest witnesses are covered too. Let `A` be a lift labelling that
differs from `hon(lambda)` at an endpoint of a `mu`-mass at most `zeta` of the
constraints. If `val(A) >= 1/2 + gamma`, then
`val(hon(lambda)) >= 1/2 + gamma - zeta`.

**Theorem 2 (tightness).** Suppose (B+) holds, and `P = NP`. Then a
polynomial-time selector exists whose lift gives `hon(lambda)` the value
`val_G(hon(lambda))`, for an outer labelling `lambda` of value `>= 1 - eps`
found by search-to-decision. Orient each constraint so that the block of the
honest seed label `hon(lambda)_(w_e)` sends it to the branch with bit
`<lambda_(a_e), x_e>`.
So whenever the composition's own completeness analysis gives
`val_G(hon(lambda)) >= 1 - eta`, the honest selector completeness is
`1 - eta`. Above `1/2`, the honest-witnessed selector hole is therefore
equivalent to NP collapsing, up to the gap between `RP` and `P`.

The proof is `efficient-branch-selectors-list-decode-honest-outer-labels-proof`.

## Consequences for the UGC cone

* **Honest witnesses are dead.** The orientation-lift decomposition reduces the
  rich 2-to-1 and UG hardness to one completeness hole: an efficient branch
  selector on proved 2-to-1 or 2-to-2 instances with lift completeness
  `1 - eta'`. Soundness is free. That hole was posted on the live bus and has
  not landed in this graph. For every LEC family, **no witness in that hole may
  be the honest encoding, or near it.** Otherwise the selector is itself an NP
  decoder. This holds whether the selector's view is view-local, parity-leaking
  or global.
* **Where it dies.** Invariant: the branch-bit advantage `gamma`. Step: fix one
  seed label by guessing it (`2^l` guesses). The selector's branch bits are
  then a fixed predictor of the linear form `<lambda_a, x>` with advantage
  `gamma/2`. Parseval leaves a list of `4/gamma^2` candidates, and random list
  decoding beats the outer soundness `s`.
* **Survivor.** A completeness witness for the lift must be *far from every
  honest encoding of a good outer labelling*. The witness must be a genuinely
  non-honest labelling of `G_g`. For each good `lambda`, it must differ from
  `hon(lambda)` on a constraint mass `zeta` large enough that the residual
  advantage `gamma - zeta` falls below the corollary's threshold. The reduction
  must prove that this labelling exists
  without making it computable. No branch-bit predictor of outer labels may be
  extractable from it. This is the non-honest-witness heretic H2 and nothing
  else.
* **Why a complexity assumption is unavoidable.** Theorem 2. Any unconditional
  kill of global selectors would prove `P != NP`.

**Scope of membership.** The theorem is for the LEC class with hypotheses
(B), (E), (M). The following argument that the
Khot--Minzer--Safra / Dinur--Khot--Kindler--Minzer--Safra 2-to-2 instances
behind `two-to-two-games-theorem` are LECs has not been checked against the
paper text here:

* The outer game is the smooth 3LIN label cover with `m = 3k`, and `<sigma, x>`
  is a subset-sum query.
* Constraints `(u, L''_u + x) -- (u', L''_(u') + x')` share a lifted
  `(l-1)`-space `L''`.
* Seed `(u, L)`, target `u'`, direction `x'` uniform off `L''_(u')`, which
  gives `tau <= 2^(l-1-3k)` plus the smoothness loss.
* `K = O(1)` by regularity.
* Outer `eps` and `s` can be driven below any function of `(l, gamma)` by
  choosing `k` large and then Hastad's `eps_0` small, keeping `l`.

This is recorded as an argument, not as an established premise.
