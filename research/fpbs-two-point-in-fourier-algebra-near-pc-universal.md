---
rg: 2
id: fpbs-two-point-in-fourier-algebra-near-pc-universal
kind: claim
title: On every nonamenable Cayley graph the two-point function lies in the Fourier algebra at parameters p_k decreasing to p_c
artifacts:
  - research/artifacts/fpbs/docs/fourier-algebra-two-point-2026-09-17.md
distinct_from:
  fpbs-two-point-lq-threshold-gap-universal: that asks for l^q summability for every q>2 near p_c; this asks for membership in A(Gamma), equivalently closability of the infinite-cluster form, which is incomparable with l^q summability and a single condition rather than a family
  fpbs-benjamini-schramm-universal: that is nonuniqueness at some p>p_c (c_0 decay); this is strictly stronger (on trees A fails on (p_2,p_u)) and also yields walk rate exactly rho, hence (IS)
---

**OPEN hole [A].**

**Statement.** There are `p_k` decreasing to `p_c` with `tau_(p_k)` in
`A(Gamma)`. Equivalently, by `fpbs-two-point-fourier-algebra-criterion`, for
each `k` the infinite-cluster form
`f -> E_(p_k) sum_(C infinite) |f(C)|^2` is closable in `l^2(Gamma)`.

**Why it matters.**

- It implies (IS) and BS (route
  `fpbs-integrated-sensitivity-via-fourier-algebra-two-point`).
- It is implied by `p_c < p_2`, and so by `p_c < p_(2->2)`.
- It holds on trees, where `p_A = p_2 > p_c`.

**Invariant.** The singular mass `s(tau_p) = dist_B(tau_p, A)`.

- It is zero at `p_c` and at most `theta(p)` above it (the criterion,
  item 3).
- [A] needs it to be exactly zero at the `p_k`, which is not a `B`-open
  condition.

## Attempts

* **Operator-algebra continuation from p_c (swarm-0917-w7).**
  - `tau_(p_c)` is in `A`, and `dist_B(tau_p, A) <= theta(p) -> 0`.
  - **Where it dies:** `A` is a closed subspace with empty interior in `B`.
    The collapse witness `f_p` of `fpbs-two-point-state-axioms-admit-collapse`
    has the same two facts and is not in `A` for every `p > p_c`.
  - So no two-point state argument, even with Fourier-algebra membership at
    `p_c`, proves [A].
  - Needed next: event-level closability of the infinite-cluster form, i.e.
    control of `E |f(C_inf)|^2` along `l^2`-null, form-Cauchy sequences.
