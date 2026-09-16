---
rg: 2
id: retracts-of-type-f-groups-are-of-type-f
kind: claim
title: "Every retract of a group of type F is of type F"
distinct_from:
  f-infinity-groups-of-finite-cd-are-of-type-f: that quantifies over F_infinity groups of finite cd; this quantifies over retracts of type F groups. The two are equivalent through retract-closure-from-f-infinity-fcd-type-f and f-infinity-fcd-type-f-from-retract-closure, but the retract form is the closure property that applies directly to free factors, direct factors and split quotients
  quasi-retracts-have-smaller-dehn-functions: that concerns Dehn functions of quasi-retracts; this concerns finiteness of classifying spaces of algebraic retracts
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Let `Γ` be of type F, and let `i: G → Γ`, `r: Γ → G` be homomorphisms with
`r∘i = id_G`. Then `G` is of type F.

Every retract of a type F group is already finitely presented, of type FP and
of finite cd, by Lemma C0 of the artifact. So this claim is the hole
`f-infinity-groups-of-finite-cd-are-of-type-f` restricted to retracts. It is
equivalent to the full hole, because every `F_∞` group of finite cd is a
retract of the type F group `G × Z`.

Equivalent forms:

- direct factors of type F groups are of type F;
- a group with a finitely dominated `K(G,1)` has a finite one;
- `σ(G) = 0` for every finitely presented group of type FP.

Special cases that hold:

- **Free factors.** If `Γ = A * B` is of type F, then `A` and `B` are of type
  F (artifact, Proposition D). The Wall class is additive,
  `σ(Γ) = ind σ(A) + ind σ(B)`, and the retractions onto the factors detect
  each summand.
- **Direct factors with a type F cofactor of Euler characteristic `±1`.** If
  `Γ = G × H` with `H` of type F and `e(H) = ±1`, then `G` is of type F
  (`g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class`).
- **Fibred retracts.** If `G` is finitely presented and maps onto `Z` with
  kernel of type FP, then `G` is of type F
  (`ascending-hnn-of-fp-group-has-zero-k0-euler-class`).

## Attempts

- **Pushing a finite resolution along the retraction.** For a finite free
  resolution `C_* → Z` over `ZΓ`, the complex `ZG ⊗_{ZΓ} C_*` (via `r`) is
  finite free over `ZG`, and its homology is `H_*(ker r; Z)`. When `ker r` is
  acyclic this is a finite free resolution of `Z`, so `G` is FL, hence of
  type F. It dies for every non-acyclic kernel, including `ker r = Z` in
  `G × Z`.
- **Pushing the Wall class along `r`.** `r_*: K_0(ZΓ) → K_0(ZG)` is a map on
  classes, but in general `σ(G)` is not `r_*σ(Γ)`. For free factors
  `Γ = G * B` the discrepancy lies in `Z·[ZG]`, so the argument works. For
  `Γ = G × H` with `H` of type F, `σ(Γ) = e(H)·ind σ(G)`, and
  `r_*σ(Γ) = e(H)·σ(G)` detects `σ(G)` only up to `e(H)`. It dies at
  `H = Z`, where `e(Z) = 0`.
- **Topology.** `K(G,1)` is a homotopy retract of a finite complex, so it is
  finitely dominated. Converting finite domination into finiteness is exactly
  Wall's obstruction `σ(G)`, so this is circular.
- **Split extensions `Γ = K ⋊ G` with `K` of type F.** A product formula of
  Gersten type would detect `σ(G)` only up to multiplication by `e(K)`. It
  dies at `e(K) = 0`, which already includes the original case `K = Z`.
- **Minimal counterexamples.** A counterexample of least cd can be taken
  one-ended (Grushko factors are retracts, plus additivity of `σ` over free
  products). It does not fibre with an FP fibre, and it has no antipodal pair
  in `Σ^d(G;Z)`
  (`f-infinity-fcd-group-with-antipodal-sigma-pair-is-type-f`). No
  construction meeting all these constraints is known.
