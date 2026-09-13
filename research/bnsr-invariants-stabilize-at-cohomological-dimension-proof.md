---
rg: 2
id: bnsr-invariants-stabilize-at-cohomological-dimension-proof
kind: route
title: "Proof that BNSR invariants stabilize at the cohomological dimension, via Novikov homology"
target: bnsr-invariants-stabilize-at-cohomological-dimension
requires: []
---

**Inputs (standard).**

1. *Novikov–Sikorav characterization.* For a connected CW complex `X` of finite
   type with `π_1 X = G`, the homological invariant `Σ^q(X;Z)` is the set of
   characters `χ` for which the Novikov–Sikorav homology
   `H_i(X; \widehat{ZG}_{-χ})` vanishes for all `i ≤ q`. Suciu,
   *Sigma-invariants and tropical varieties*, arXiv:2010.07499, abstract: "The
   Bieri-Neumann-Strebel-Renz invariants Σ^q(X,ℤ)⊂H^1(X,ℝ) of a connected,
   finite-type CW-complex X are the vanishing loci for Novikov-Sikorav homology
   in degrees up to q". The group invariant is `Σ^q(G;Z) = Σ^q(K(G,1);Z)` for
   a finite-type `K(G,1)` (going back to Sikorav for q = 1, and to Bieri and to
   Farber–Geoghegan–Schütz in general).
2. *Homotopical versus homological.* For `G` of type `F_n` and `n ≥ 2`,
   `Σ^n(G) = Σ^2(G) ∩ Σ^n(G;Z)`, recorded as equation (2.1) of
   Molyneux–Nucinkis–Santos Rego, arXiv:2309.12213 (going back to Renz and
   Bieri–Renz).

**Homological part.** `G` is of type `F_∞`, so it has a `K(G,1)` of finite
type, and `H_i(K(G,1); M) = Tor_i^{ZG}(M, Z)` for every right `ZG`-module `M`.
Since `cd G = d`, the trivial module `Z` has projective dimension `d` over `ZG`,
so `Tor_i^{ZG}(M,Z) = 0` for all `i > d` and all `M`, in particular for the
Novikov ring `M = \widehat{ZG}_{-χ}`. By input 1, for `m ≥ d` the condition
"`H_i = 0` for `i ≤ m`" is the same as "`H_i = 0` for `i ≤ d`", so
`Σ^m(G;Z) = Σ^d(G;Z)`.

**Homotopical part.** Put `m_0 = max(d,2)` and let `m ≥ m_0`. By input 2,
`Σ^m(G) = Σ^2(G) ∩ Σ^m(G;Z)` and `Σ^{m_0}(G) = Σ^2(G) ∩ Σ^{m_0}(G;Z)`. Both
`m` and `m_0` are `≥ d`, so the homological part gives
`Σ^m(G;Z) = Σ^{m_0}(G;Z) = Σ^d(G;Z)`, hence `Σ^m(G) = Σ^{m_0}(G)`.

**Openness.** `Σ^∞(G) = ∩_m Σ^m(G) = Σ^{m_0}(G)`, and `Σ^{m_0}(G)` is open
(Bieri–Neumann–Strebel 1987, Renz 1988, as recorded in Ershov–Zaremsky
arXiv:2505.18826 §2.1: "Σ^m(G) is open in 𝕊(G) for all m < ∞"). Likewise
`Σ^∞(G;Z) = Σ^d(G;Z)` is open. ∎

**Check of the degree convention.** For `G = F_2^r` (`d = r`) the invariants
are `Σ^m(F_2^r)^c = {χ nonzero on at most m factors}` (Meier–Meinert–VanWyk),
which stabilize exactly at `m = r`. So the index `d` in the homological
statement cannot be lowered in general.
