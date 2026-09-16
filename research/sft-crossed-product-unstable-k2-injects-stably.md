---
rg: 2
id: sft-crossed-product-unstable-k2-injects-stably
kind: claim
title: For a finitely presented free minimal Z^2-SFT crossed product, some unstable Steinberg kernel in rank at least four injects into stable K_2
distinct_from:
  aperiodic-subshift-ring-unstable-k2-vanishes: that asks for vanishing of K_2(n, LC(Y,F_2) ⋊ Z) in d = 1; this is d = 2, where the kernel is nonzero in every rank, and only injectivity into K_2(R) is asked.
  leavitt-tensor-steinberg-kernel-is-stable-k2: that proves centrality and stability of the unstable kernel over Leavitt tensor hosts; this is the same stability question over a tracial Z^2 crossed product, where no Leavitt factor is available.
  rigid-sft-elementary-group-mod-centre-is-fp: that is finite normal generation of K_2(n,R); this is the stability half only.
---

**OPEN.** Let `Ω` be a free minimal `Z^2`-SFT such that `R = LC(Ω, F_q) ⋊ Z^2` is finitely
presented. Then there is `n >= 4` such that the stabilization map `K_2(n,R) -> K_2(R)` is injective.

## Attempts

- **Injective stability theorems need stable rank (literature, not verified at theorem level).**
  - Van der Kallen, *Injective stability for K_2* (LNM 551, 1976), and Suslin--Tulenbaev (Zap. Nauchn.
    Sem. LOMI 64, 1976) give injectivity of `K_2(n,R) -> K_2(R)` once `n` is large compared to the
    Bass stable rank of `R`.
  - The Weibel K-book form quoted in `elementary-groups-over-polynomial-f-p-rings-are-fp-proof` is
    stated for `sr(R) = d + 1` and `n >= d + 3`.
  - **Where it dies.** No bound on `sr(LC(Ω, F_q) ⋊ Z^2)` is known here. Even the `Z` case is open in
    the graph (`minimal-cantor-crossed-product-has-stable-rank-at-most-two`,
    `subshift-crossed-product-ring-has-bass-stable-rank-at-most-two`).
- **Centrality first.**
  - Voronetsky, *Centrality of K_2-functor revisited* (arXiv:2004.08551, 2020), proves that
    `St(n,A)` is a crossed module over `GL(n,A)` under a local stable rank condition on an algebra `A`
    over a commutative ring. *Locally isotropic Steinberg groups I* (arXiv:2410.14039, v2 22 Nov 2024)
    does the same for Steinberg groups of locally isotropic reductive groups. Both abstracts were
    re-read on 2026-09-16; the theorem statements were not.
  - **Where it dies.** The centre of `R` is `F_q` for free minimal `Ω`. So localizing at primes of the
    centre does nothing, and the local stable rank condition is a global stable rank bound on `R`,
    which is not known.
- **Vanishing is not an option.** `z2-crossed-product-steinberg-kernel-is-nonzero` shows
  `K_2(n,R) ≠ 0` for every `n >= 3`, with a class that survives to `K_2(R)`. So the kernel of the
  stabilization map is the only thing in question.
