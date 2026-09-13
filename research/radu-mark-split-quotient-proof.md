---
rg: 2
id: radu-mark-split-quotient-proof
kind: route
title: Split quotients of Radu's lattice keeping the mark, from the finite residual and the slab sign character
target: radu-mark-survives-only-in-non-rf-split-quotients
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-horizontal-quotient-is-arithmetic-lattice
  - radu-delta-squared-orbit-is-signed-permutation-module
  - radu-square-lamp-forces-reflections-in-finite-actions
---

Notation of the target. `N ◁ Γ_R`, `δ^4 ∉ N`, `M = NK` of finite index, `B = K/(N ∩ K)`.

**Inputs.**
* `radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2: `(xz)^4` lies in the finite residual
  of `Γ_R`, i.e. in every finite-index normal subgroup.
* `radu-horizontal-quotient-is-arithmetic-lattice`: `K = ker ρ` is a normal subgroup with quotient
  `Q`, an infinite cocompact lattice.
* `radu-delta-squared-orbit-is-signed-permutation-module`, items 1–2: for `h ∈ H_Γ`,
  `h δ^2 h^(−1) = δ^(2ψ'(h))`, and `ψ'` descends to `H_Q = ρ(H_Γ)`.
* `radu-square-lamp-forces-reflections-in-finite-actions`, item 2: every finite-index normal
  subgroup `S ◁ Q` contains some `h ∈ H_Q ∩ S` with `ψ'(h) = −1`.

**1. Not residually finite.** Every finite quotient of `Γ_R/N` is a finite quotient of `Γ_R`, so
it kills `δ^4`. If `Γ_R/N` were residually finite, `δ^4` would be trivial in it, i.e. `δ^4 ∈ N`,
contrary to hypothesis. A finite group is residually finite, so `Γ_R/N` is infinite.

**2. Splitting.** `N` and `K` are normal in `Γ_R`, hence so are `M = NK` and `N ∩ K`. In
`M/(N ∩ K)` the images `K/(N ∩ K)` and `N/(N ∩ K)` are normal, intersect trivially and generate
the group, so it is their internal direct product. The second isomorphism theorem gives
`B = K/(N ∩ K) ≅ NK/N = M/N`, which has finite index in `Γ_R/N` because `M` has finite index in
`Γ_R`. A finite-index subgroup of the finitely generated group `Γ_R/N` is finitely generated.

**3. Sign reversal.** `S := ρ(M) = M/K` is a normal subgroup of `Q` (as `M ◁ Γ_R`) of finite
index. Pick `h ∈ H_Q ∩ S` with `ψ'(h) = −1`, and a lift `h̃ ∈ H_Γ` with `ρ(h̃) = h`. Since
`ρ(h̃) ∈ ρ(M)` and `K = ker ρ ⊆ M`, we have `h̃ ∈ M`. Write `h̃ = n k` with `n ∈ N`, `k ∈ K`.
Modulo `N`, `h̃ ≡ k`, so

```text
k δ^2 k^(−1)  ≡  h̃ δ^2 h̃^(−1)  =  δ^(2ψ'(h̃))  =  δ^(−2)      (mod N),
```

using `ψ'(h̃) = ψ'(h) = −1`. Here `δ^2 ∈ K` (`radu-horizontal-quotient-is-arithmetic-lattice`:
`(xz)^2` is among the normal generators of `Λ_v`), so this is a conjugation inside `B`. In the
abelianization `B^ab` it reads `[δ^2] = −[δ^2]`, so `[δ^4] = 2[δ^2] = 0`, i.e. `δ^4 ∈ [B,B]`. If `B`
were abelian, then `δ^4 = 1` in `B ≅ M/N`, i.e. `δ^4 ∈ N`, contrary to hypothesis. So `B` is not
abelian.

**Consequence.** If `Γ_R/N` is amenable and `ρ(N)` has finite index in `Q`, then `M = NK` has
finite index (as `M/K = ρ(N)`), and 1–3 apply. QED
