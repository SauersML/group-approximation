---
rg: 2
id: sparse-full-group-kazhdan-pair-gives-mixing-nonsofic-action
kind: claim
title: A Kazhdan infranormal pair in the full group of a free mixing action, with sparse Γ-orbits and one non-normal conjugate orbit, yields a free mixing nonsofic action through a Bernoulli extension over the Γ-orbit relation
distinct_from:
  mixing-relation-hosts-noninvariant-kazhdan-pair: that asks for a non-invariant fixed algebra on the mixing action itself; this asks only for a sparsity estimate and one conjugate that leaves Γ-orbits, and manufactures the non-invariance and keeps mixing through an extension
  kun-thom-free-nonsofic-action: that uses the generalized Bernoulli action over L/Γ, which is not mixing because Γ fixes a coset; this uses a Bernoulli extension over the orbit relation of a full-group copy of Γ, which is mixing exactly when that copy is sparse
  compact-extension-kazhdan-fixed-algebras-are-blind: that shows compact extensions cannot create non-invariant fixed algebras; this extension is Bernoulli over a subrelation, not compact, and creates them
---

**ESTABLISHED.** Let `G` be a countable sofic group and `G ↷ (X,μ)` an essentially free mixing p.m.p. action with
orbit relation `R_G`. Let `Γ <= L` be countable groups, both Kazhdan, with `Γ` infranormal in `L` and `L` sofic. Let
`ρ : L → [R_G]` be a homomorphism and `R' = R_(ρ(Γ))`. Assume

* **(a) sparsity:** `p(g) := μ{x : gx ∈ ρ(Γ)x} → 0` as `g → ∞` in `G`;
* **(b) a conjugate leaves Γ-orbits:** for some `l ∈ L` and `γ ∈ Γ`, `μ{y : ρ(l^(-1)γl)y ∉ ρ(Γ)y} > 0`.

Let `Y` be the Bernoulli extension of `X` over `R_G/R'`: points `(x, ω)` with `ω ∈ {0,1}^([x]_(R_G)/R')`, measure `μ`
times fair coin products, and `g(x,ω) = (gx, ω)`. Then `G ↷ Y` is essentially free, mixing and **not sofic**. So
(a) and (b) settle `mixing-free-nonsofic-action-of-sofic-group`.

**This is a reduction, one direction.** The flagship follows from the existence of a sparse pair. The converse is not
claimed.

**Automatic cases.**

* (b) holds whenever `ρ` is free and `Γ` is not normal in `L`. It fails when `ρ(L)` has finite orbits
  (`haagerup-hosts-blind-full-group-kazhdan-certificate`, Step 6).
* (a) holds whenever `ρ(Γ)` has finite orbits a.e. It fails whenever `ρ(Γ)` contains a subgroup of `G` acting with
  infinite orbits, in particular for `ρ = id`, which recovers the non-mixing Kun--Thom action.

**Where hosts can live.** By `haagerup-hosts-blind-full-group-kazhdan-certificate`, `G` is not Haagerup and `ρ(L)` has
infinite orbits on a set of positive measure. Two regimes:

1. **Finite Γ-orbits: dead.** Where `ρ(Γ)`-orbits are finite, every `ρ(l)` permutes them, so (b) fails there (proof,
   Step 6.6). The set in (b) must consist of points with infinite `ρ(Γ)`-orbits.
2. **Twisted product design: survives, with constraints.** Take `G = L × M`, a free mixing p.m.p. action
   `G ↷ X`, and a Borel cocycle `β : L × X → M` over the action it defines, `ρ(l)x = (l, β(l,x))·x`, that is
   `β(l_1 l_2, x) = β(l_1, ρ(l_2)x) β(l_2, x)`. Since `L` and `M` commute, `ρ` is a homomorphism into `[R_G]`.
   * *Warning: the plain product is not an example.* A coordinatewise action on `X_L × X_M` is never mixing for
     `L × M`: functions of `x_2` are invariant under `L × {1}`. So `L` must move the `M`-coordinates. Skew products
     `(l x_1, β(l,x_1) x_2)` over a coordinatewise `G`-action are excluded.
   * `ρ` is free, so (b) holds for every non-normal `Γ`.
   * (a) says exactly that `sup_m μ{β(γ,·) = m} → 0` as `γ → ∞` in `Γ`. For bounded `γ` and `m → ∞`, it holds
     automatically, because `m ↦ μ{β(γ,·) = m}` is a probability vector.
   * *Constraint: `M` is not Haagerup.* For Haagerup `M`, (T) makes every cocycle of `Γ` into `M` uniformly tight,
     `μ{β(γ,·) ∈ F} >= 1/2` for a finite `F` and all `γ` (proof, Step 7).
   * *Constraint: `β|Γ` is not cohomologous to a homomorphism when `ρ(Γ)` is mixing.* Where it is, (a) fails
     (proof, Step 8). So `ρ(Γ)` is not a mixing s-malleable action, for example a diffuse Bernoulli action (Popa's
     cocycle superrigidity).

The existence question is `sparse-noninvariant-kazhdan-pair-in-non-haagerup-host`.

**Why this is new.** Every earlier Theorem C design fixes the action and looks for a non-invariant fixed algebra. The
blindness theorems kill that on mixing actions, their factors and compact extensions. Here the extension manufactures
the non-invariance from a purely combinatorial orbit condition (b), while (a) controls mixing. The analytic question
becomes a counting question about orbits of a full-group copy.

Proof: `sparse-full-group-kazhdan-pair-proof`.
