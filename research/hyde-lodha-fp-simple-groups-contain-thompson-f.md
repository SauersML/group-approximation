---
rg: 2
id: hyde-lodha-fp-simple-groups-contain-thompson-f
kind: claim
title: The finitely presented simple Hyde--Lodha groups Q_n contain Thompson's group F
distinct_from:
  hyde-lodha-groups-contain-thompson-commutator-subgroup: that is about the finitely generated but not finitely presented groups G_rho of arXiv:1807.06478, which contain F' by construction, and it lists the finitely presented groups of arXiv:2302.04805 as unchecked; this is the finitely presented family Q_n = [Gamma_n, Gamma_n], where F must be found inside the commutator subgroup of a Higman--Thompson stabilizer.
  hyde-lodha-periodic-simple-groups-are-not-amenable: that proves non-amenability and a free subgroup for Q_2 through a circle-measure argument; this finds Thompson's F inside every Q_n, which transfers nonhyperlinearity and nonsoficity of F upward.
  thompson-f-is-a-subgroup-of-lodha-moore-group: that locates F inside the Lodha--Moore group of piecewise projective homeomorphisms; this locates F inside the piecewise linear 1-periodic simple groups Q_n.
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

**ESTABLISHED** by route `hyde-lodha-fp-simple-groups-contain-thompson-f-proof`. Not
independently reviewed.

**Statement.** For every `n ≥ 2`, the Hyde--Lodha group `Q_n = [Γ_n, Γ_n]` of arXiv:2302.04805
contains a subgroup isomorphic to Thompson's group `F`. By Theorem 1.3 there, `Q_n` is
finitely presented, of type `F_∞`, and simple.

**Consequences.**

- If `F` is not hyperlinear, respectively not sofic, then no `Q_n` is. Both properties pass to
  subgroups.
- With `S = Q_n` as the simple input of the Fournier--Facio construction,
  `thompson-f-is-not-hyperlinear` implies `fournier-facio-simple-factor-not-hyperlinear`. This
  is route `fournier-facio-simple-factor-via-thompson-f`.
- A proof that some `Q_n` is hyperlinear would prove `thompson-f-is-hyperlinear`.

**Explicit copy.** Put `η = n(n+1)`, and let `f ∈ F_η` be the bump with nodes `(0,0)`,
`(η^{-2}, η^{-1})`, `(1 − η^{-1}, 1 − η^{-2})`, `(1,1)`. Put `u = f ∘ f`, let `v_1` be `f`
rescaled onto `[η^{-1}, 2η^{-1}]` and `v_2` be `f` rescaled onto `[2η^{-1} − η^{-2}, 2η^{-1}]`.

- Then `k_i = [u, v_i^{-1}] = u^{-1} v_i u v_i^{-1}` lie in `[F_η, F_η]`.
- The group `⟨k_1, k_2⟩` contains `F`.
- It maps into `Q_n` through the isomorphism of `F_η` with `Stab_{Γ_n}(0)`, which is HL
  Proposition 1.4(2).
- The supports and orbitals are checked in exact arithmetic for `n = 2, ..., 6` by
  `experiments/fournier-facio-simple-factor-corner-2026-09-16/check_thompson_f_commutators.py`.
