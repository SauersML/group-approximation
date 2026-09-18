---
rg: 2
id: free-orbit-label-lift-fibre-count-proof
kind: route
title: Fibres over finite label configurations have size a power of |F|, so injectivity bounds the count, and a conserved count makes the lift surjective
target: free-orbit-label-lifts-need-count-raising-label-automata
requires:
  - finite-injective-positive-charge-automata-are-surjective
artifacts:
  - experiments/affine-relay-lifts-2026-09-17/check.py
---

Notation as in the target. Write `μ` for the local rule of `τ`, with memory `M ∋ 1`.

**Import, verbatim** (`finite-injective-positive-charge-automata-are-surjective`): "Let tau:A^G->A^G be a cellular
automaton fixing the all-zero configuration. [...] Suppose: 1. For every finite x, sum_g w(tau(x)(g))=sum_g w(x(g)).
2. Tau is injective on the set of finite configurations. Then tau is bijective on the finite configurations of each
prescribed total charge and is surjective on A^G." Here `w(0)=0` and `w(a)>0` for `a≠0`.

**Item 1.**
- `θ(0^G)` is fixed by every translation, so it is a constant configuration `c^G`.
- It is fixed by `F`, since `0^G` is and `θ` commutes with `F`. So `c` is `F`-fixed, and `c = 0`.
- Then `τ(0^G) = σθ(0^G) = 0^G`, so `μ(0^M) = 0`.
- If `ℓ` is `0` off a finite set `S`, then `τ(ℓ)(g) ≠ 0` forces `gM ∩ S ≠ ∅`, i.e. `g ∈ S M^(-1)`.

**Item 2.**
- **Fibre sizes.** For a finite label configuration `ℓ`, the fibre `σ^(-1)(ℓ)` consists of the `c` with `c(h) = 0` off
  the active sites of `ℓ` and `c(h)` in the orbit `ℓ(h)` at active sites. Orbits are free, so each has `|F|` elements
  and `|σ^(-1)(ℓ)| = |F|^|ℓ|`.
- **Fibres go to fibres.** `σθ = τσ` gives `θ(σ^(-1)(ℓ)) ⊆ σ^(-1)(τ(ℓ))`.
- **Count.** Fibres over distinct `ℓ` are disjoint and `θ` is injective. So the fibres over all finite `ℓ` with
  `τ(ℓ) = m` inject into `σ^(-1)(m)`. That gives the displayed inequality. Keeping one term gives
  `|F|^|ℓ| <= |F|^|τ(ℓ)|`, and `|F| >= 2` gives `|ℓ| <= |τ(ℓ)|`.

**Item 3.** Suppose `|τ(ℓ)| = |ℓ|` for every finite `ℓ`.
- **`τ` is injective on finite configurations.** If `τ(ℓ) = τ(ℓ') = m` with `ℓ ≠ ℓ'` finite, the inequality of item 2
  has two terms, each equal to `|F|^|m|`, and the sum exceeds `|F|^|m|`. That is impossible.
- **Charge theorem.** Take `w(0) = 0` and `w(b) = 1` for `b ∈ B`. By item 1 `τ` fixes `0^G`, it conserves `w` on
  finite configurations, and it is injective on them. By the import, every finite label configuration `m` equals
  `τ(ℓ)` for some finite `ℓ`, and then `|ℓ| = |m|`.
- **Fibres are covered.** `θ` maps `σ^(-1)(ℓ)` injectively into `σ^(-1)(m)`, and both sets have `|F|^|m|` elements.
  So `σ^(-1)(m) ⊆ θ(C^G)` for every finite `m`.
- **Density.** The union of these fibres is the set of configurations equal to `0` off a finite set. It is dense:
  extend any finite pattern by `0`.
- **Closed image.** `θ` is continuous and `C^G` is compact, so `θ(C^G)` is closed. It contains a dense set, so it is
  all of `C^G`.

So a non-surjective `θ` raises the count on some finite `ℓ`, and by item 2 it never lowers it. Nothing about `G` is
used, and the local rule of `θ`, in particular its phase rule, is arbitrary.

**Calibration** (`experiments/affine-relay-lifts-2026-09-17/check.py`). Over `C_n`, for lifts of label shifts, the
inequality `|τ(ℓ)| >= |ℓ|` is asserted for every label configuration (it holds with equality, as it must, since `τ` is
bijective there).
