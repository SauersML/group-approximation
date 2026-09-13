---
rg: 2
id: central-halving-trivializes-every-closed-bauer-face-bundle
kind: claim
title: Asymptotically central halving on all traces trivializes the W*-bundle over every closed set of extreme traces
distinct_from:
  r-fibre-bundle-triviality-iff-uniform-central-halving: that is Ozawa's criterion inside an abstract bundle; this is a hypothesis on the C*-algebra, checked on all of T(A), which yields triviality over every closed face at once, Bauer or not globally.
  bauer-uniform-gamma-iff-trivial-tracial-bundle: that equates uniform Gamma with triviality when T(A) is Bauer; this assumes the weaker unbalanced halving condition and needs no Bauer hypothesis on T(A).
  point-dominated-diagonal-ah-has-uniform-gamma: that proves full uniform Gamma for a class of diagonal AH systems; this proves only face triviality, under central halving without balancing against other elements.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Let `A` be unital, separable and nuclear, with no finite-dimensional representation.
Suppose `A` has **central halving** (CH): positive contractions `p_n ∈ A` with

```text
‖p_n − p_n²‖_{2,T(A)} → 0,    sup_{τ∈T(A)} |τ(p_n) − 1/2| → 0,    ‖[p_n, a]‖_{2,T(A)} → 0  for all a ∈ A.
```

Then for every nonempty closed `K ⊆ ∂_e T(A)`:
- the W*-bundle `M_K` of `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` is
  trivial, `M_K ≅ C_σ(K,R)`;
- the unit of `A` is tracially `N`-divisible relative to `K` for every `N`.

**What CH omits.** Uniform property Γ at `n = 2` also asks
`sup_τ |τ(a p_n) − τ(a)/2| → 0` for every `a`. CH does not. Over a closed set of
extreme traces the balancing is automatic: Ozawa's proof of Theorem 15
(ii) ⟹ (iii) derives `‖E(p_n a) − E(p_n)E(a)‖ → 0` from factoriality of the fibres
by Dixmier approximation. Over non-closed families of traces it can fail
(`toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces`).

**Model test.** `C([0,1])` fails CH, because at `δ_x` the value `p_n(x)` would have
to be near both `{0,1}` and `1/2`. Toms's no-Γ algebra satisfies CH
(`block-balanced-towers-have-central-halving`).

**Credit.** The mechanism, half of the diagonal blocks as a central projection, is
Castillejos–Evington–Tikuisis–White, arXiv:1912.04207, Proposition 5.10. That result
covers diagonal AH algebras with trivial units and Bauer `T(A)`, through their
Proposition 3.1.
