---
rg: 2
id: non-large-characteristic-linear-sofic-group-exists
kind: claim
title: Some countable group has no rank-ultraproduct embedding over finite fields of characteristic tending to infinity
distinct_from:
  non-finite-field-linear-sofic-group-exists: that forbids rank models over all finite fields; this forbids them only in large characteristic, so a witness may still be F_p-linear sofic for finitely many p.
  non-linear-sofic-group: that is failure over one fixed field; this is failure over every sequence of finite fields whose characteristic tends to infinity, which implies failure over C and over Q.
  group-not-linear-sofic-in-any-positive-characteristic-exists: that is the fixed-characteristic component of the root; this is the large-characteristic component.
---

**OPEN.** Some countable `H` is not in `L_inf`. That is, `H` embeds in no rank ultraproduct
`prod_omega GL_(n_i)(F_(q_i)) / N_omega` with `char F_(q_i) -> infinity` along `omega`. Definitions are on
`root-splits-into-large-and-fixed-characteristic-witnesses`.

**Role.** This is component (a) of the characteristic split.
- The root holds iff this holds together with `group-not-linear-sofic-in-any-positive-characteristic-exists`.
- Given such an `H`, the root only needs non-`F_p`-linear-sofic groups for the finitely many primes `p` in `S(H)`.

**Equivalent model form.** For some finite `W <= H` and `eps > 0`, only finitely many characteristics carry a
`(W, eps)`-model with separation `1/4` (Lemma 3 of the split proof).

## Attempts

- **Class-killing constraints (2026-09-17, lane `sw-024`)**, from
  `c-linear-sofic-iff-bounded-dimension-large-characteristic`.
  - *No algebraic certificate.* Large-characteristic models give a Sylvester matrix rank function on `K[H]` with
    `K ≅ C` and `rk(g - 1) >= 1/4`. Every group algebra `C[H]` carries one with `rk(g - 1) >= 1/2`, the von Neumann
    rank. So stable-finiteness, zero-divisor or idempotent certificates cannot prove this claim for any `H`.
  - *Only unbounded wild models matter.* Suppose `H` is not complex-linear sofic. Then `H` witnesses this claim iff
    some window's minimal model dimension over `F_l` is not eventually finite as `l -> infinity`, and on that window
    every model is wild.
    - "Minimal model dimension" means the smallest dimension of a `(W, eps)`-model.
    - "Wild" means the characteristic divides the order of the generated finite group.
    - The dimension gate already makes this minimal dimension tend to infinity. What must be proved is that it
      becomes infinite.
  - *Consequence.* A proof must exploit a metric phenomenon of large-dimensional modular representations, as in the
    rank-stability and width routes. Formal algebra over `C[H]` cannot supply it.
- **Bridge question (spark, not pursued).** If `L_inf` equals complex-linear soficity, this claim is equivalent to the
  existence of a group that is not complex-linear sofic. By the dimension gate, that equality says that normalized
  rank data realizable in growing dimension over `F_l` for infinitely many `l` is approximately realizable over `C`.
  - This is a group-level analogue of whether the closed cones of normalized subspace-arrangement rank vectors in
    characteristic `l` converge to the characteristic-zero cone as `l -> infinity`.
