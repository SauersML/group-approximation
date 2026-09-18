---
rg: 2
id: sparse-noninvariant-kazhdan-pair-in-non-haagerup-host
kind: claim
title: Some free mixing action of a sofic group carries a full-group Kazhdan infranormal pair with sparse Γ-orbits and a conjugate that leaves them
distinct_from:
  mixing-relation-hosts-noninvariant-kazhdan-pair: that needs a non-invariant fixed algebra on the host itself, which forces non-ergodic Kazhdan copies; this needs only the orbit conditions (a) and (b), and the host fixed algebra may be trivial
  f2xf2-admits-mixing-nonsofic-action: that fixes the acting group; this cannot use F2 x F2 or any Haagerup group
---

**OPEN.** There are:

* a countable sofic group `G` with an essentially free mixing p.m.p. action `G ↷ (X,μ)`;
* countable sofic Kazhdan groups `Γ <= L`, with `Γ` infranormal in `L`;
* a homomorphism `ρ : L → [R_G]`;

such that

* **(a)** `μ{x : gx ∈ ρ(Γ)x} → 0` as `g → ∞`, and
* **(b)** `μ{y : ρ(l^(-1)γl)y ∉ ρ(Γ)y} > 0` for some `l ∈ L` and `γ ∈ Γ`.

By `sparse-full-group-kazhdan-pair-gives-mixing-nonsofic-action`, this settles
`mixing-free-nonsofic-action-of-sofic-group`.

**Proved constraints** (`sparse-full-group-kazhdan-pair-proof`, Step 6, and
`haagerup-hosts-blind-full-group-kazhdan-certificate`):

* `G` is not Haagerup, and `ρ(L)` has infinite orbits on a set of positive measure.
* `ρ(Γ)` contains no translations by an infinite subgroup of `G`.
* The set in (b) lies, up to a null set, where `ρ(Γ)`-orbits are infinite. Designs with finite `ρ(Γ)`-orbits are
  dead.
* If `ρ(Γ)` is mixing, its cocycle into `G` is not cohomologous to a homomorphism.

**Concrete form (twisted product design).** The following statement implies this claim:

> There are sofic Kazhdan groups `Γ <= L`, with `Γ` infranormal and not normal, a sofic group `M`, a free mixing
> p.m.p. action `L × M ↷ X`, and a Borel map `β : L × X → M` that is a cocycle over `ρ(l)x = (l, β(l,x))·x`, i.e.
> `β(l_1 l_2, x) = β(l_1, ρ(l_2)x) β(l_2, x)`, with `sup_(m ∈ M) μ{x : β(γ,x) = m} → 0` as `γ → ∞` in `Γ`.

Take `G = L × M`. Then (a) and (b) hold (`sparse-full-group-kazhdan-pair-gives-mixing-nonsofic-action`, regime 2).
Necessary conditions:

* `L × {1}` must move the `M`-part of `X`. A coordinatewise action on `X_L × X_M`, and so every skew product
  `(l x_1, β(l,x_1) x_2)` over it, is never mixing for `L × M`, since functions of `x_2` are `L × {1}`-invariant.
* `M` is not Haagerup (Step 7).
* If `ρ(Γ)` is mixing, `β|Γ` is not cohomologous to a homomorphism (Step 8), so `ρ(Γ)` is not a diffuse Bernoulli
  action.

The problem is to find an anti-concentrating cocycle of a Kazhdan group into a non-Haagerup group `M`, over an action
that is not s-malleable, and to couple it with a mixing `M`-action that `L` also moves. The analytic half has a model:
for a proper `ψ : L → H` into a semisimple group with the Howe--Moore property and a lattice `Λ < H`, the return cocycle
`β(l,x) = s(lx)^(-1)ψ(l)s(x)` of `L ↷ H/Λ` (with `s` a Borel section) satisfies
`μ{β(γ,·) = λ} = ⟨π(ψ(γ)^(-1),λ^(-1))1_D, 1_D⟩_(L^2(H))` for the two-sided regular representation `π` of `H × H` and a
fundamental domain `D`. This is uniformly small as `γ → ∞` by Howe--Moore for `H × H`. The missing half is a free mixing
`L × Λ`-action that `ρ` embeds into, which the plain product does not provide.
