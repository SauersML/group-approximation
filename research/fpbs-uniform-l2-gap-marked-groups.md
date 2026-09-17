---
rg: 2
id: fpbs-uniform-l2-gap-marked-groups
kind: claim
title: The l2 gap holds with constants depending only on the number of generators and the spectral gap
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for a finite critical l2 bound on each nonamenable transitive graph with a graph-dependent constant; this asks, for Cayley graphs only, for one pair (M,delta) serving every k-marked group with spectral radius at most 1-eta.
  fpbs-l2-gap-baire-dichotomy: that proves the uniform version is equivalent to emptiness of the first derivative of X_(k,eta); this is the conjecture that it is empty.
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
---

**OPEN.** For every `k >= 2` and `eta in (0,1)` there are `M < infinity` and
`delta > 0` such that every `k`-marked group `(Gamma; s_1,...,s_k)` whose simple
Cayley graph `G` has spectral radius at most `1 - eta` satisfies

```text
||T^G_{p_c(G) + delta}||_{2->2} <= M.
```

This is Section 4 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

* It implies `fpbs-benjamini-schramm-universal` (Proposition 4.2 there). Every
  nonamenable Cayley graph is the Cayley graph of some marked group in some
  `X_{k,eta}`, and Corollary 3.2 of
  `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md` turns the bound
  into `p_c < p_c + delta <= p_{2->2} <= p_u`.
* By `fpbs-l2-gap-baire-dichotomy`, it is equivalent to every point of
  `X_{k,eta}` having a neighbourhood in some `U_{M,delta}`.
* By `fpbs-high-girth-uniform-l2-patch`, it is equivalent to uniform constants
  on each of the finitely many relator cylinders `Z_{k,eta,w}` with
  `|w| < L(eta)`.
* It is a **stronger conjecture** than the Cayley-graph case of the pointwise
  l2 gap. The pointwise version only needs the transfinite kernel `K_{k,eta}`
  to be empty.
* Compactness makes it the exact form in which Corollary 3.2 transplants gaps
  to local limits.

Hutchcroft's known classes (hyperbolic, nonunimodular, acylindrically
hyperbolic, free products) give qualitative gaps. None of them certifies a
fixed `(M,delta)` on an open set of marked groups. No counterexample is known.

## Attempts

* **Spectral data alone: walk counting plus Cheeger thinning (2026-09-17,
  sketch).**
  - Test functions `1_F` give `|∂_E F|/|F| >= d(1-rho) >= d eta` on a
    `d`-regular graph. So `fpbs-expansion-thinning-threshold` gives
    `p_c <= 1/(1+d eta)`.
  - Proposition 3.0 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`
    bounds `||T_q||` explicitly for `q < 1/((d-1)rho)`.
  - Both bounds depend only on `(d,eta)`. So uniform constants follow whenever
    `(d-1)(1-eta) < 1 + d eta`, that is, `eta > (d-2)/(2d-1)`, for every
    `d <= 2k`. The worst case `d = 2k` gives `eta > (2k-2)/(4k-1)`.

  **Where it dies:** every `d`-regular transitive graph has
  `rho >= 2 sqrt(d-1)/d`, the tree value. So this regime is nonempty only when
  `1 - sqrt(2k-1)/k > (2k-2)/(4k-1)`, which first holds at `k = 6`, and even
  then only in a thin window of `eta` near the free-group value. For small
  `eta`, spectral radius and expansion do not force `p_c (d-1) rho < 1`. Any
  proof in the small-`eta` range must use geometry beyond the two spectral
  numbers, as the girth patch does.
